module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle374
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle328
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle331
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle399
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle356
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle398
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle404
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle400
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle060
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle401
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle403
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle402
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle056
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricLevelsCharactersDoubleCosetsAgreeRation

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LevIdx

theorem core {D : D7} (S : HSp D) (N : Lat S) (hN : IsSelfDualC S N) {r : ℕ} (k : Fin r → Type) [∀ i, Field (k i)]
    [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)]
    (q : (i : Fin r) → SplitPt D (k i)) (Y : Fin r → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (F : (i : Fin r) → GlobalTheory.LocMod.Frame (k i) S.rank (Y i))
    (hinj : Function.Injective fun i => (q i).v)
    (hlat : ∀ i, IntIn (q i) S (F i) N) (J : (i : Fin r) → Subgroup (GL (Y i) (k i)))
    (hJ : ∀ i, J i ≤ GlobalTheory.SplitWeil.KO (k i) (Y i)) (hJo : ∀ i, IsOpen (J i : Set (GL (Y i) (k i))))
    (μ : Measure (GfC S)) [μ.IsHaarMeasure] (U U' : Subgroup (GA D S)) (b : GA D S) (hb : b ∈ GfC S) (hU : U ≤ GfC S)
    (hUc : IsCompact (U : Set (GA D S))) (hUo : IsOpen ((U.subgroupOf (GfC S) : Subgroup (GfC S)) : Set (GfC S)))
    (hK : ∀ κ, InK S N (fun p => ∃ i, (q i).v = p) κ → κ ∈ U)
    (hM : ∀ g ∈ U, Moves S g N N (fun p => ∃ i, (q i).v = p))
    (hU' : ∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i (x : GL (Y i) (k i)), (mt S g).map (q i).pr = (F i).β * x.val * (F i).γ → x ∈ J i) :
    μ.real {g | b * g.1 * b⁻¹ ∈ U'} * ∏ i, ((J i).relIndex (GlobalTheory.SplitWeil.KO (k i) (Y i)) : ℝ) =
      μ.real {g | b * g.1 * b⁻¹ ∈ U} := by
  set φ : GA D S →* ((i : Fin r) → GL (Y i) (k i)) := MonoidHom.pi fun i => locHom (q i) S (F i) with hφ
  have hφi : ∀ g i, φ g i = locHom (q i) S (F i) g := fun _ _ => rfl
  have hU'' : ∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i, φ g i ∈ J i := by
    intro g
    rw [hU' g]
    refine and_congr_right fun _ => forall_congr' fun i => ?_
    refine ⟨fun h => h _ ((eq_locHom_iff _ _ _ _ _).2 rfl), fun h x hx => ?_⟩
    rw [(eq_locHom_iff _ _ _ _ _).1 hx]; exact h
  have hle : U' ≤ U := fun g hg => ((hU'' g).1 hg).1

  have hidx : U'.relIndex U = ∏ i, (J i).relIndex (GlobalTheory.SplitWeil.KO (k i) (Y i)) := by
    refine GlobalTheory.T.relIndex_eq_prod_relIndex_of_surjective_pi φ U U' (fun i => GlobalTheory.SplitWeil.KO (k i) (Y i)) J hJ ?_ ?_ hU''
    · intro g hg i
      exact GlobalTheory.T.mem_integralGL_split_place_of_carries_latticeCompletion (q i) S (F i) N _ ⟨i, rfl⟩ (hlat i) g (hM g hg) _ ((eq_locHom_iff _ _ _ _ _).2 rfl)
    · intro x hx
      obtain ⟨g, hg, hgx⟩ := GlobalTheory.T.exists_selfDual_stabilizer_with_prescribed_splitPlace_matrices S N hN k q Y F hinj hlat x hx
      refine ⟨g, hK g hg, funext fun i => ?_⟩
      rw [hφi]; exact ((eq_locHom_iff _ _ _ _ _).1 (hgx i)).symm

  let cj : GfC S →* GfC S :=
    { toFun := fun g => ⟨b * g.1 * b⁻¹, (GfC S).mul_mem ((GfC S).mul_mem hb g.2) ((GfC S).inv_mem hb)⟩
      map_one' := by ext1; simp
      map_mul' := fun g h => by ext1; simp [mul_assoc] }
  have hcj : Continuous cj :=
    Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  have hcjb : Function.Bijective cj := by
    refine ⟨fun g h e => ?_, fun g => ⟨⟨b⁻¹ * g.1 * b, (GfC S).mul_mem ((GfC S).mul_mem ((GfC S).inv_mem hb) g.2) hb⟩, ?_⟩⟩
    · have := congrArg Subtype.val e
      ext1; simpa [cj] using this
    · ext1; simp [cj, mul_assoc]
  set H := (U.subgroupOf (GfC S)).comap cj
  set H' := (U'.subgroupOf (GfC S)).comap cj
  have eH : {g : GfC S | b * g.1 * b⁻¹ ∈ U} = (H : Set (GfC S)) := rfl
  have eH' : {g : GfC S | b * g.1 * b⁻¹ ∈ U'} = (H' : Set (GfC S)) := rfl
  have hHH' : H'.relIndex H = U'.relIndex U := by
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hcjb.2, Subgroup.relIndex_subgroupOf hU]

  have hHc : IsCompact (H : Set (GfC S)) := by
    rw [Topology.IsInducing.subtypeVal.isCompact_iff]
    have e : Subtype.val '' (H : Set (GfC S)) = (fun g => b⁻¹ * g * b) '' (U : Set (GA D S)) := by
      ext y; constructor
      · rintro ⟨g, hg, rfl⟩
        exact ⟨b * g.1 * b⁻¹, hg, by simp [mul_assoc]⟩
      · rintro ⟨u, hu, rfl⟩
        refine ⟨⟨b⁻¹ * u * b, (GfC S).mul_mem ((GfC S).mul_mem ((GfC S).inv_mem hb) (hU hu)) hb⟩, ?_, rfl⟩
        change b * (b⁻¹ * u * b) * b⁻¹ ∈ U
        simpa [mul_assoc] using hu
    convert hUc.image ((continuous_const.mul continuous_id).mul continuous_const) using 1
    exact e

  have hU'o : IsOpen ((U'.subgroupOf (GfC S) : Subgroup (GfC S)) : Set (GfC S)) := by
    have e : ((U'.subgroupOf (GfC S) : Subgroup (GfC S)) : Set (GfC S)) =
        ((U.subgroupOf (GfC S) : Subgroup (GfC S)) : Set (GfC S)) ∩
          ⋂ i, (fun g : GfC S => locHom (q i) S (F i) g.1) ⁻¹' (J i : Set (GL (Y i) (k i))) := by
      ext g
      simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
      rw [hU'']
      rfl
    rw [e]
    exact hUo.inter (isOpen_iInter_of_finite fun i =>
      (hJo i).preimage ((continuous_locHom (q i) S (F i)).comp continuous_subtype_val))
  have hH'o : IsOpen (H' : Set (GfC S)) := hU'o.preimage hcj
  have hH'H : H' ≤ H := fun g hg => hle hg
  rw [eH, eH', ← Nat.cast_prod, ← hidx, ← hHH']
  exact vol_mul_relIndex μ H H' hH'H hHc hH'o

end GlobalTheory.LevIdx

theorem GlobalTheory.LevIdx.vol_level_eq : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : GlobalTheory.QPl.QFam v t), F.Pins w → (∀ j, j < D.R.m → IsSelfDualC (c.V j) (v.N j) → ∀ (μ : Measure (GfC (c.V j))), μ.IsHaarMeasure → ∀ (U U' : Subgroup (GA D (c.V j))) (b : GA D (c.V j)), b ∈ GfC _ → U ≤ GfC _ → IsCompact (U : Set (GA D (c.V j))) → IsOpen ((U.subgroupOf (GfC _) : Subgroup (GfC (c.V j))) : Set (GfC (c.V j))) → (∀ κ, InK _ (v.N j) (· ∈ w.Q) κ → κ ∈ U) → (∀ g ∈ U, Moves _ g (v.N j) (v.N j) (· ∈ w.Q)) → (∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i d hd x, (mt _ g).map (F.Q i).q.pr = ((F.Q i).FY j d hd).β * x.val * ((F.Q i).FY j d hd).γ → x ∈ ((F.Q i).T.lev j d hd).J) → μ.real {g | b * g.1 * b⁻¹ ∈ U'} * ∏ i, ((F.Q i).idx j : ℝ) = μ.real {g | b * g.1 * b⁻¹ ∈ U}) ∧ (IsSelfDualC c.T v.NT → (∀ i, IsOpen ((F.Q i).T.levTop.J : Set (GL (F.Q i).Z (F.Q i).k))) → ∀ (μ : Measure (GfC c.T)), μ.IsHaarMeasure → ∀ (U U' : Subgroup (GA D c.T)) (b : GA D c.T), b ∈ GfC _ → U ≤ GfC _ → IsCompact (U : Set (GA D c.T)) → IsOpen ((U.subgroupOf (GfC _) : Subgroup (GfC c.T)) : Set (GfC c.T)) → (∀ κ, InK _ v.NT (· ∈ w.Q) κ → κ ∈ U) → (∀ g ∈ U, Moves _ g v.NT v.NT (· ∈ w.Q)) → (∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i (x : GL (F.Q i).Z (F.Q i).k), (mt _ g).map (F.Q i).q.pr = (F.Q i).FT.β * x.val * (F.Q i).FT.γ → x ∈ (F.Q i).T.levTop.J) → μ.real {g | b * g.1 * b⁻¹ ∈ U'} * ∏ i, ((F.Q i).idx D.R.m : ℝ) = μ.real {g | b * g.1 * b⁻¹ ∈ U}) := by
  intro D c v t w F hP
  have hQ : (· ∈ w.Q) = fun p => ∃ i, (F.Q i).q.v = p := funext fun p => propext (hP.places p)
  have hs : ∀ i, (F.Q i).s + 1 + 1 = D.R.m := fun i => (F.Q i).hs
  refine ⟨fun j hj hN μ hμ U U' b hb hU hUc hUo hK hM hU' => ?_, fun hN hTo μ hμ U U' b hb hU hUc hUo hK hM hU' => ?_⟩
  · let d : Fin F.r → ℕ := fun i => (F.Q i).s + 1 - j
    have hd : ∀ i, j + d i = (F.Q i).s + 1 := fun i => by have := hs i; simp only [d]; omega
    rw [hQ] at hK hM
    have key := GlobalTheory.LevIdx.core (c.V j) (v.N j) hN (fun i => (F.Q i).k) (fun i => (F.Q i).q) (fun i => (F.Q i).X j ⊕ Fin (d i))
      (fun i => (F.Q i).FY j (d i) (hd i)) hP.inj (fun i => (F.Q i).latY j (d i) (hd i))
      (fun i => ((F.Q i).T.lev j (d i) (hd i)).J) (fun i => (F.Q i).le j (d i) (hd i))
      (fun i => ((F.Q i).reg.2.2 j (d i) (hd i)).1) μ U U' b hb hU hUc hUo hK hM ?_
    · have e : ∀ i, (F.Q i).idx j = (((F.Q i).T.lev j (d i) (hd i)).J).relIndex (GlobalTheory.SplitWeil.KO (F.Q i).k _) :=
        fun i => (F.Q i).idx_mid j (d i) (hd i)
      simp only [e]
      exact key
    · intro g
      rw [hU' g]
      refine and_congr_right fun _ => forall_congr' fun i => ⟨fun h x hx => h (d i) (hd i) x hx, fun h d' hd' x hx => ?_⟩
      obtain rfl : d' = d i := by have := hd i; omega
      exact h x hx
  · rw [hQ] at hK hM
    have key := GlobalTheory.LevIdx.core c.T v.NT hN (fun i => (F.Q i).k) (fun i => (F.Q i).q) (fun i => (F.Q i).Z)
      (fun i => (F.Q i).FT) hP.inj (fun i => (F.Q i).latT)
      (fun i => (F.Q i).T.levTop.J) (fun i => (F.Q i).leT) hTo μ U U' b hb hU hUc hUo hK hM hU'
    have e : ∀ i, (F.Q i).idx D.R.m = ((F.Q i).T.levTop.J).relIndex (GlobalTheory.SplitWeil.KO (F.Q i).k _) :=
      fun i => by rw [← hs i]; exact (F.Q i).idx_top
    simp only [e]
    exact key

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.LatIdemVac

variable {D : D7}

theorem latO_at_le {S T : HSp D} (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (v : Pl D) : latO S T LS LT (· = v) ≤ latO S T LS LT fun _ => True := by
  unfold latO
  refine AddSubgroup.closure_mono ?_
  rintro w ⟨α, hα, -, rest⟩
  exact ⟨α, hα, fun _ h => absurd trivial h, rest⟩

theorem pairA_zero_mul (a b : Af D.host.F) :
    pairA D.host.F 0 a * pairA D.host.F 0 b = pairA D.host.F 0 (a * b) := by
  show ((0 : Ainf D.host.F), a) * ((0 : Ainf D.host.F), b) = ((0 : Ainf D.host.F), a * b)
  rw [Prod.mk_mul_mk, mul_zero]

theorem placeIdem_mul_mem {S T : HSp D} (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {v : Pl D} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    (Matrix.of fun i j => algebraMap (AF D.host.F) (AE D) ε * u i j : WO S T) ∈ latO S T LS LT (· = v) := by
  obtain ⟨α₀, rfl, h1, h0⟩ := hε
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α₀ * α, fun w => ?_, fun w hw => ?_, a, ha, s, hs, t, ht, ?_⟩
    · rw [map_mul]
      by_cases hwv : w = v
      · subst hwv; rw [h1, one_mul]; exact hα w
      · rw [h0 w hwv, zero_mul]; exact zero_mem _
    · rw [map_mul, h0 w hw, zero_mul]
    · ext i j
      simp only [Matrix.of_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        Algebra.algebraMap_self, RingHom.id_apply, pairA_zero_mul]
  | zero =>
    convert (latO S T LS LT (· = v)).zero_mem using 1
    ext i j; simp
  | add x y _ _ hx hy =>
    convert add_mem hx hy using 1
    ext i j; simp only [Matrix.of_apply, Matrix.add_apply, mul_add]
  | neg x _ hx =>
    convert neg_mem hx using 1
    ext i j; simp only [Matrix.of_apply, Matrix.neg_apply, mul_neg]

theorem splitIdem_mul_mem {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : SplitPt D k) {S T : HSp D} (LS : Lat S) (LT : Lat T) {u : WO S T}
    (hu : u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    u.map (fun a => q.e * a) ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) := by
  obtain ⟨ε, hε, hsum⟩ := q.above
  have h := (GlobalTheory.SplitVac.idem_latO D k q S T LS LT _ (placeIdem_mul_mem _ _ hε hu)).1
  convert h using 1
  ext i j
  simp only [Matrix.map_apply, Matrix.of_apply]
  rw [← hsum, ← mul_assoc, mul_add, q.split.1, q.split.2.1, add_zero]

end GlobalTheory.LatIdemVac

namespace GlobalTheory.LatIdemVac

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
  {S T : HSp D} {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

def tensorWith (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Ψ : Matrix Y Y' k → ℂ) :
    (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun Φ := p.tensorAt FS FT Φ Ψ
  map_add' Φ Φ' := by
    funext t
    simp only [Place.tensorAt, Pi.add_apply, add_mul]
  map_smul' c Φ := by
    funext t
    simp only [Place.tensorAt, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem tensorWith_apply (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Ψ : Matrix Y Y' k → ℂ) (Φ : WO S T → ℂ) :
    tensorWith p FS FT Ψ Φ = p.tensorAt FS FT Φ Ψ := rfl

theorem tensorAt_trans (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {e : AE D} (he : e * p.e = 0)
    (Φ : WO S T → ℂ) (Ψ : Matrix Y Y' k → ℂ) {x : WO S T} (hx : IsHalf e x) :
    p.tensorAt FS FT (fun t => Φ (t + x)) Ψ = fun t => p.tensorAt FS FT Φ Ψ (t + x) := by
  funext t
  simp only [Place.tensorAt]
  rw [GlobalTheory.LocMod.Witness.down_add p FS FT t x, GlobalTheory.LocMod.TOneModel.down_half_zero p FS FT he hx, add_zero,
    sub_add_eq_add_sub]

theorem tensorAt_modul (ψ : AddChar (AF D.host.F) ℂ) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {e : AE D}
    (he : e * p.e = 0) (Φ : WO S T → ℂ) (Ψ : Matrix Y Y' k → ℂ) {y : WO S T} (hy : IsHalf (cA D e) y) :
    p.tensorAt FS FT (fun t => ψ (symplO S T t y) * Φ t) Ψ = fun t => ψ (symplO S T t y) * p.tensorAt FS FT Φ Ψ t := by
  funext t
  simp only [Place.tensorAt]
  rw [GlobalTheory.LocMod.TOneModel.symplO_sub_half p he t (GlobalTheory.LocMod.Witness.up_half p FS FT _) hy, mul_assoc]


open Classical in
theorem tensorAt_halfInd (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {e : AE D} (he : e * p.e = 0)
    (Λ Λv : AddSubgroup (WO S T)) (hle : Λv ≤ Λ) (hstab : ∀ t ∈ Λ, t.map (fun a => p.e * a) ∈ Λv) :
    p.tensorAt FS FT ((1 : ℂ) • halfInd e Λ) (Set.indicator {x | p.up FS FT x ∈ Λv} fun _ => 1) =
      (1 : ℂ) • halfInd (e + p.e) Λ := by
  funext t
  simp only [one_smul, Place.tensorAt]
  rw [GlobalTheory.LocMod.TOneModel.up_down_eq p FS FT t, Set.indicator_apply]
  simp only [Set.mem_setOf_eq, GlobalTheory.LocMod.TOneModel.up_down_eq p FS FT t]
  set M : WO S T := t.map (fun a => p.e * a) with hMdef
  have key : ((t - M ∈ Λ ∧ IsHalf e (t - M)) ∧ M ∈ Λv) ↔ (t ∈ Λ ∧ IsHalf (e + p.e) t) := by
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨by simpa using add_mem h1 (hle h3), fun i j => ?_⟩
      have h := h2 i j
      simp only [hMdef, Matrix.sub_apply, Matrix.map_apply] at h
      linear_combination h + t i j * he
    · rintro ⟨h1, h2⟩
      have h3 : M ∈ Λv := hstab t h1
      refine ⟨⟨sub_mem h1 (hle h3), fun i j => ?_⟩, h3⟩
      simp only [hMdef, Matrix.sub_apply, Matrix.map_apply]
      linear_combination h2 i j - t i j * he
  unfold halfInd
  by_cases hR : t ∈ Λ ∧ IsHalf (e + p.e) t
  · obtain ⟨⟨h1, h2⟩, h3⟩ := key.2 hR
    rw [if_pos hR, if_pos ⟨h1, h2⟩, if_pos h3, mul_one]
  · rw [if_neg hR]
    by_cases h3 : M ∈ Λv
    · rw [if_pos h3, mul_one, if_neg fun h => hR (key.1 ⟨h, h3⟩)]
    · rw [if_neg h3, mul_zero]

end GlobalTheory.LatIdemVac

namespace GlobalTheory.LatIdemVac

theorem isPlaceModel_tensorLat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (M : Lat S) (M' : Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (P : LocPl ψ S T M M') (e : AE D), e * P.q.e = 0 → ∀ (f₀ : WO S T → ℂ) (T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) (e + P.q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 f₀ T' → ∃ T'' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 f₀ T'' ∧ ∀ Φ, T'' Φ = T' ((ofSplit P.q).tensorAt P.FS P.FT Φ (Set.indicator {x | (ofSplit P.q).up P.FS P.FT x ∈ latO S T (M : Set _) (M' : Set _) (· = P.q.v)} fun _ => 1)) := by
  intro D ψ S T M M' hM hM' P e he f₀ T' hT'
  set p := ofSplit P.q with hp
  set Ψ : Matrix P.Y P.Y' P.k → ℂ :=
    Set.indicator {x | p.up P.FS P.FT x ∈ latO S T (M : Set _) (M' : Set _) (· = P.q.v)} fun _ => 1 with hΨ
  have hpe : p.e = P.q.e := rfl
  have he' : e * p.e = 0 := he
  have hΨsb : Ψ ∈ SB (Matrix P.Y P.Y' P.k) := GlobalTheory.T.indicator_localHomLattice_mem_schwartzBruhat D ψ S T M M' hM hM' P
  have hsb : ∀ Φ, IsSBHalf e (latO S T (M : Set _) (M' : Set _) fun _ => True) Φ →
      IsSBHalf (e + P.q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) (p.tensorAt P.FS P.FT Φ Ψ) :=
    fun Φ hΦ => GlobalTheory.T.schwartzBruhatHalf_tensor_split_place_selfDual D ψ S T M M' hM hM' P e he Φ hΦ Ψ hΨsb
  refine ⟨T' ∘ₗ tensorWith p P.FS P.FT Ψ, ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩, fun Φ => rfl⟩
  · rw [LinearMap.comp_apply, tensorWith_apply, tensorAt_trans p P.FS P.FT he' Φ Ψ hx]
    exact hT'.trans _ (hsb Φ hΦ) x (GlobalTheory.LocMod.TOneModel.half_sum p he' hx)
  · rw [LinearMap.comp_apply, tensorWith_apply, tensorAt_modul p ψ P.FS P.FT he' Φ Ψ hy]
    exact hT'.modul _ (hsb Φ hΦ) y (GlobalTheory.LocMod.TOneModel.half_sum_conj p he' hy)
  · rw [LinearMap.comp_apply, tensorWith_apply, tensorAt_halfInd p P.FS P.FT he' _ _ (latO_at_le _ _ P.q.v)
      (fun t ht => splitIdem_mul_mem P.q M M' ht)]
    exact hT'.vac

end GlobalTheory.LatIdemVac

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel


theorem _root_.GlobalTheory.T.isThetaFunO_splitPlaces_schrodingerModel_sum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (M : Lat S) (M' : Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (n : ℕ) (L : Fin n → LocPl ψ S T M M'), (Function.Injective fun i => (L i).q.v) → ∀ (f₀ : WO S T → ℂ) (T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), Vac ψ S T M M' (fun _ => True) f₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) (∑ i, (L i).q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) 1 f₀ T' → ∀ Φ, IsSBHalf (∑ i, (L i).q.e) (latO S T (M : Set _) (M' : Set _) fun _ => True) Φ → IsThetaFunO ψ S T (T' Φ) := by
  first | exact @GlobalTheory.PlaceSumTheta.isThetaFunO_sum_placeModel | exact GlobalTheory.PlaceSumTheta.isThetaFunO_sum_placeModel | (intros; apply GlobalTheory.PlaceSumTheta.isThetaFunO_sum_placeModel <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitLat

theorem exists_selfDual_frames : ∀ (D : D7) (S : HSp D) (L₀ : GlobalTheory.FinPl.Lat S), IsSelfDualC S L₀ → ∀ (I : Type) [Finite I] (K : I → Type) [∀ i, Field (K i)] [∀ i, ValuativeRel (K i)] [∀ i, TopologicalSpace (K i)] [∀ i, IsNonarchimedeanLocalField (K i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (K i)) (Y : I → Type) [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)] (F : ∀ i, GlobalTheory.LocMod.Frame (K i) S.rank (Y i)), (∀ i i', (q i).v = (q i').v → i = i') → ∃ L : GlobalTheory.FinPl.Lat S, IsSelfDualC S L ∧ ∀ i, IntIn (q i) S (F i) L := by
  intro D S L₀ hL₀ I _ K _ _ _ _ q Y _ _ F hinj
  have key : ∀ s : Finset I, ∃ L : GlobalTheory.FinPl.Lat S, IsSelfDualC S L ∧ ∀ i ∈ s, IntIn (q i) S (F i) L := by
    intro s
    refine Finset.induction_on s ⟨L₀, hL₀, by simp⟩ ?_
    intro j s hj ih
    obtain ⟨L, hL, hs⟩ := ih
    obtain ⟨L', hL', hother, hq⟩ := GlobalTheory.T.exists_selfDualLattice_prescribed_splitPlace D (K j) (q j) S (Y j) (F j) L hL
    refine ⟨L', hL', ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · exact hq
    · have hne : (q i).v ≠ (q j).v := fun h => hj (by obtain rfl := hinj i j h; exact hi')
      have h1 := hs i hi'
      unfold IntIn at h1 ⊢
      rw [hother _ hne]
      exact h1
  haveI := Fintype.ofFinite I
  obtain ⟨L, hL, h⟩ := key Finset.univ
  exact ⟨L, hL, fun i => h i (Finset.mem_univ i)⟩

end GlobalTheory.SplitLat
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.reducesToResidue_of_localLevelElement_movedBack : ∀ {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E) (b : GA D (c.V 0)) (β : GL (Fin (c.V 0).rank) (Lev.EAf D)), GlobalTheory.LevZero.LocAt G PP b β → b ∈ GfC (c.V 0) → ∀ (hr : D.R.r ≤ (c.V 0).rank) (g : GA D (c.V 0)) (x : G.S.P.J), (ofSplit G.q).IsLoc (G.FY 0 (G.s + 1) (Nat.zero_add _)) g (GlobalTheory.LevZeroGen.upZero G.S (Fin D.R.t) x.1) → finE (c.V 0) (b⁻¹ * g * b) ∈ Formalism.L2.DIV.St β → GlobalTheory.LevZero.Red G PP x (upperLeftBlock hr (redFn β PP (finE (c.V 0) (b⁻¹ * g * b)))) := by
  first | exact @GlobalTheory.LevZeroFamRead.red_of_isLoc | exact GlobalTheory.LevZeroFamRead.red_of_isLoc | (intros; apply GlobalTheory.LevZeroFamRead.red_of_isLoc <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

theorem _root_.GlobalTheory.T.stabilizes_selfDual_iff_frame_matrix_stabilizes : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k) (A : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p A n) (L : GlobalTheory.FinPl.Lat A) (Λ : Submodule 𝒪[k] (n → k)), IsSelfDualC A L → β.IsLat L Λ → ∀ κ : GA D A, (GlobalTheory.FinPl.Moves A κ L L (· = p.v) ↔ coordHom A p.pr β.b β.b' β.bb' β.b'b κ • Λ = Λ) := by
  first | exact @GlobalTheory.FrameMoves.moves_iff_smul | exact GlobalTheory.FrameMoves.moves_iff_smul | (intros; apply GlobalTheory.FrameMoves.moves_iff_smul <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix ValuativeRel Formalism.L2.Col
open scoped Classical

namespace GlobalTheory.QPl.RatOrb
open GlobalTheory.StepData GlobalTheory.SplitWeil GlobalTheory.TwBridge.Lev GlobalTheory.TwBridge.LevOrb

theorem image_val_mem_nhds {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {B : Type} [Fintype B] [DecidableEq B] {S : Set (GL B k)} (hS : IsOpen S) {h : GL B k} (hh : h ∈ S) :
    Units.val '' S ∈ nhds h.val := by
  obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.1 hS
  have hd : h.val.det ≠ 0 := h.det_ne_zero
  have hc : ContinuousAt (Inv.inv : Matrix B B k → Matrix B B k) h.val := by
    refine continuousAt_matrix_inv _ ?_
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hd
  have hG : ContinuousAt (fun N : Matrix B B k => (N, MulOpposite.op N⁻¹)) h.val :=
    continuousAt_id.prodMk (MulOpposite.continuous_op.continuousAt.comp hc)
  have key : ∀ u : GL B k, Units.embedProduct _ u = (u.val, MulOpposite.op u.val⁻¹) := fun u => by
    rw [Units.embedProduct_apply, Matrix.coe_units_inv]
  have h1 := hG.preimage_mem_nhds (hW.mem_nhds (by rw [← key]; exact hh))
  have h2 : {N : Matrix B B k | N.det ≠ 0} ∈ nhds h.val :=
    (isOpen_ne.preimage (continuous_id.matrix_det)).mem_nhds hd
  filter_upwards [h1, h2] with N hN1 hN2
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero N hN2, ?_, rfl⟩
  rw [Set.mem_preimage, key]
  exact hN1

theorem exists_rat_of_sameOrb : ∀ {E k : Type} [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (ι : E →+* k) (ϖ : kˣ), GlobalTheory.SymBridge.IsCompl P (qOf P) ι ϖ → ∀ {A : Type} [Fintype A] [DecidableEq A] {n : ℕ} (e : A ≃ Fin n) (Jl : Subgroup (GL (A ⊕ Fin 0) k)), IsOpen (Jl : Set (GL (A ⊕ Fin 0) k)) → Jl ≤ GlobalTheory.SplitWeil.KO k (A ⊕ Fin 0) → ∀ (M : ℕ) (c : (A → k) ⧸ GlobalTheory.StepData.box A (ϖ ^ M)) (y₀ : Sp E n), GlobalTheory.QPl.SameOrb Jl (GlobalTheory.StepData.box A (ϖ ^ M)) c (Submodule.Quotient.mk fun a => ι (y₀ (e a))) → ∃ r ∈ GLint E n P, ∃ g ∈ Jl, g.val.toBlocks₁₁ = GlobalTheory.SymBridge.toLoc ι e e r.toLinearMap ∧ ∀ y : Sp E n, ((qOf P : E) ^ M)⁻¹ • (r.symm y - y₀) ∈ stdAt E n P → c = Submodule.Quotient.mk fun a => ι (y (e a)) := by
  intro E k _ _ _ _ _ _ _ P ι ϖ hc A _ _ n e Jl hJo hJ M c y₀
  rintro ⟨g₀, hg₀, y₁, rfl, hy⟩
  rw [Submodule.Quotient.eq] at hy
  let e' : A ⊕ Fin 0 ≃ Fin n := (Equiv.sumEmpty A (Fin 0)).trans e
  have he : ∀ a, e' (.inl a) = e a := fun a => rfl
  have h0 : (g₀⁻¹).val.toBlocks₁₁ *ᵥ (fun a => ι (y₀ (e a))) - y₁ ∈ box A (ϖ ^ M) := by
    have := neg_mem (GlobalTheory.TwBridge.LevOrb.mulVec_mem_box (hJ (inv_mem hg₀)) _ hy)
    rwa [mulVec_sub, mulVec_mulVec, ← CoupStab.toBlocks₁₁_mul, Units.inv_mul, CoupStab.toBlocks₁₁_one, one_mulVec,
      neg_sub] at this
  have hU2 : IsOpen {N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k |
      N.toBlocks₁₁ *ᵥ (fun a => ι (y₀ (e a))) - y₁ ∈ box A (ϖ ^ M)} := by
    refine (CoupStab.isOpen_box (ϖ ^ M)).preimage (f := fun N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k =>
      N.toBlocks₁₁ *ᵥ (fun a => ι (y₀ (e a))) - y₁) ?_
    have hb : Continuous fun N : Matrix (A ⊕ Fin 0) (A ⊕ Fin 0) k => N.toBlocks₁₁ :=
      continuous_pi fun i => continuous_pi fun j => continuous_apply_apply (Sum.inl i) (Sum.inl j)
    exact (hb.matrix_mulVec continuous_const).sub continuous_const
  obtain ⟨U, hU, hUo, hUm⟩ := mem_nhds_iff.1 (image_val_mem_nhds hJo (inv_mem hg₀))
  obtain ⟨M₀, ⟨a1, a2⟩, -⟩ := exists_approx ι hc.dense (g₀⁻¹).val (hUo.inter hU2) ⟨hUm, h0⟩
  obtain ⟨g, hg, ev⟩ := hU a1
  obtain ⟨r, hr⟩ := exists_phi ι e' M₀ g ev
  refine ⟨r, (GlobalTheory.VolBridge.mem_stabL_stdAt_iff_locHom_mem_KO P ι hc.int e' r).2 ?_, g, hg, ?_, fun y hy' => ?_⟩
  · rw [show GlobalTheory.VolBridge.locHom ι e' r = phi ι e' r from Units.ext rfl, hr]
    exact hJ hg
  · rw [← hr]
    rfl
  · have h1 := GlobalTheory.TwBridge.LevOrb.mulVec_mem_box (hJ hg) _ ((mem_box_iff hc e M _).2 hy')
    rw [Set.mem_setOf_eq, ← ev] at a2
    rw [← hr, phi_mulVec e e' he] at h1 a2
    rw [eq_comm, Submodule.Quotient.eq]
    convert add_mem h1 a2 using 1
    ext a
    simp only [Pi.sub_apply, Pi.add_apply, map_sub, LinearEquiv.apply_symm_apply]
    abel

end GlobalTheory.QPl.RatOrb
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing

theorem _root_.GlobalTheory.T.splitPlace_changeBaseVacuum_heisenbergCombination : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (S T : HSp D) (α : Frame p S n') (β : Frame p T n) (LS MS : Lat S) (LT MT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC S MS → IsSelfDualC T MT → (∀ (ΛS : Submodule 𝒪[k] (n' → k)) (ΛT : Submodule 𝒪[k] (n → k)), α.IsLat MS ΛS → β.IsLat MT ΛT → ∀ f₀ g, Over ψ α β LS LT f₀ (latInd ΛS ΛT) g → Vac ψ S T MS MT (· = p.v) g ∧ ∀ Ψ f, Over ψ α β LS LT f₀ Ψ f → Over ψ α β MS MT g Ψ f) ∧ ∀ Ψ ∈ SB (Matrix n n' k), ∃ c : WO S T →₀ ℂ, CombAt (· = p.v) c ∧ ∀ f₀, Vac ψ S T LS LT (· = p.v) f₀ → Over ψ α β LS LT f₀ Ψ (comb ψ S T c f₀) := by
  first | exact @GlobalTheory.FinPl.Rebase.rebase | exact GlobalTheory.FinPl.Rebase.rebase | (intros; apply GlobalTheory.FinPl.Rebase.rebase <;> assumption)
end
