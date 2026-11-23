module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle001
import GroundTheory.LocalFields.Bundle002
import GroundTheory.LocalFields.PadicLogSeries
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.pieceStab_of :
    HopGal → PieceStab := by
  intro hG l _ k _ hl H hfet Ω _ _ L _ _ θ σ x hx
  simp only [piece, Submodule.mem_iInf] at hx ⊢
  intro g
  obtain ⟨d, hd⟩ := hfet g
  have hc := hG l k hl H Ω g d hd σ
  have hxg := hx g
  rw [Module.End.mem_eigenspace_iff] at hxg ⊢
  have e : (LinearMap.baseChange L (hop l H Ω g)) ((galV l H Ω L σ) x)
      = (galV l H Ω L σ) ((LinearMap.baseChange L (hop l H Ω g)) x) := by
    show ((LinearMap.baseChange L (hop l H Ω g)) ∘ₗ (LinearMap.baseChange L (galTot l Ω H.q σ))) x
      = ((LinearMap.baseChange L (galTot l Ω H.q σ)) ∘ₗ (LinearMap.baseChange L (hop l H Ω g))) x
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hc]
  rw [e, hxg, map_smul]
end

section

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.stabOpen_of :
    HtDesc → StabOpen := by
  intro h l _ k Ω _ _ _ _ X p hqc hqs n i x m
  obtain ⟨L, hL, z, hz⟩ := h (l ^ m) k Ω p hqc hqs n i (x.1 m)
  have fix : ∀ τ ∈ L.fixingSubgroup,
      GlobalTheory.EtC.pull (ZMod (l ^ m)) (sch.map (galMap Ω p τ)) (tw (l ^ m) i) n (x.1 m) = x.1 m := by
    intro τ hτ
    rw [← hz, ← GlobalTheory.EtC.pull_comp, ← Functor.map_comp, LateralTheory.EWeil.StabPf.galMap_proj L p τ hτ]
  rw [isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨(fun g => g * σ⁻¹) ⁻¹' (L.fixingSubgroup : Set _), ?_, ?_, ?_⟩
  · intro g hg
    have hg' : g * σ⁻¹ ∈ L.fixingSubgroup := hg
    have e : g = (g * σ⁻¹) * σ := by group
    show ((galHl l Ω p n i g) x).1 m = x.1 m
    rw [e, map_mul, Module.End.mul_apply]
    change GlobalTheory.EtC.pull (ZMod (l ^ m)) (sch.map (galMap Ω p (g * σ⁻¹))) (tw (l ^ m) i) n
      (((galHl l Ω p n i σ) x).1 m) = x.1 m
    have hσ' : ((galHl l Ω p n i σ) x).1 m = x.1 m := hσ
    rw [hσ']
    exact fix _ hg'
  · exact (IntermediateField.fixingSubgroup_isOpen L).preimage (continuous_mul_const σ⁻¹)
  · show σ * σ⁻¹ ∈ L.fixingSubgroup
    rw [mul_inv_cancel]
    exact one_mem _
end

section

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.Int.Geo

private def blk (k : Type) [Field k] {d : ℕ} (c : Fin d → ℕ) (i : ℕ) : Submodule k (Fin d → k) where
  carrier := {v | ∀ j, c j ≠ i → v j = 0}
  zero_mem' _ _ := rfl
  add_mem' ha hb j h := by simp [ha j h, hb j h]
  smul_mem' r v hv j h := by simp [hv j h]

theorem grSS_of :
    GrHom → SSOfSum → GrSS := by
  intro _ hSS Γ k _ _ d ρ₀ ρ c hJH hρ
  obtain ⟨hinv, hmax⟩ := hJH
  have key : ∀ (g : Γ) (i : ℕ) (u : Fin d → k), u ∈ blk k c i → ∀ a,
      (↑(ρ g) : Matrix (Fin d) (Fin d) k).mulVec u a =
        if c a = i then (↑(ρ₀ g) : Matrix (Fin d) (Fin d) k).mulVec u a else 0 := by
    intro g i u hu a
    simp only [Matrix.mulVec, dotProduct, hρ]
    split_ifs with h
    · refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs with h'
      · rfl
      · simp [hu b (by omega)]
    · refine Finset.sum_eq_zero fun b _ => ?_
      split_ifs with h'
      · simp [hu b (by omega)]
      · simp
  have hblk : ∀ i, IsInv ρ (blk k c i) := by
    intro i g u hu j hj
    rw [key g i u hu j, if_neg hj]
  have hsup : ⨆ i, blk k c i = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun j _ => ?_
    refine Submodule.mem_iSup_of_mem (c j) ?_
    intro a ha
    rw [Pi.single_eq_of_ne]
    rintro rfl
    exact ha rfl
  refine hSS Γ k d ρ (fun i => blk k c i) hblk ?_ hsup
  intro i U hU hUle
  have hlow : low k c i ≤ low k c (i + 1) := fun v hv j hj => hv j (by omega)
  have hblkle : blk k c i ≤ low k c (i + 1) := fun v hv j hj => hv j (by omega)
  have hdisj : ∀ v, v ∈ blk k c i → v ∈ low k c i → v = 0 := by
    intro v h1 h2
    funext j
    by_cases h : c j = i
    · exact h2 j h.ge
    · exact h1 j h
  have hU'inv : IsInv ρ₀ (low k c i ⊔ U) := by
    intro g v hv
    obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp hv
    rw [Matrix.mulVec_add]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (hinv i g w hw)) ?_
    have huB := hUle hu
    rw [← sub_add_cancel ((↑(ρ₀ g) : Matrix (Fin d) (Fin d) k).mulVec u)
      ((↑(ρ g) : Matrix (Fin d) (Fin d) k).mulVec u)]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right (hU g u hu))
    intro a ha
    rw [Pi.sub_apply, key g i u huB a]
    split_ifs with h
    · exact sub_self _
    · rw [hinv (i + 1) g u (hblkle huB) a (by omega), sub_zero]
  rcases hmax i _ hU'inv le_sup_left (sup_le hlow (hUle.trans hblkle)) with h | h
  · left
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    have hv' : v ∈ low k c i := by
      rw [← h]
      exact Submodule.mem_sup_right hv
    exact hdisj v (hUle hv) hv'
  · right
    apply le_antisymm hUle
    intro v hv
    have hv' : v ∈ low k c i ⊔ U := by
      rw [h]
      exact hblkle hv
    obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp hv'
    have hwB : w ∈ blk k c i := by
      have := Submodule.sub_mem _ hv (hUle hu)
      simpa using this
    rw [hdisj w hwB hw, zero_add]
    exact hu

end UpperTheory.Gal.Int.Geo
end

section

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.contGL_of :
    ContGL := by
  intro Γ k _ _ _ _ _ _ d ρ
  constructor
  · intro hρ i j
    exact (Units.continuous_val.comp hρ).matrix_elem i j
  · intro h
    have hval : Continuous fun g : Γ => ((ρ g : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) :=
      continuous_matrix h
    rw [Units.continuous_iff]
    refine ⟨hval, ?_⟩
    have hinv : (fun g : Γ => (((ρ g)⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k)) =
        fun g => ((ρ g⁻¹ : GL (Fin d) k) : Matrix (Fin d) (Fin d) k) := by
      funext g
      rw [map_inv]
    rw [hinv]
    exact hval.comp continuous_inv
end

section

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.flagMove_of :
    FlagMove := by
  intro Γ k _ _ d ρ W P W' hW' hJH
  have hPP : ∀ w : Fin d → k, (↑P : Matrix (Fin d) (Fin d) k).mulVec
      ((↑(P⁻¹) : Matrix (Fin d) (Fin d) k).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hPP' : ∀ w : Fin d → k, (↑(P⁻¹) : Matrix (Fin d) (Fin d) k).mulVec
      ((↑P : Matrix (Fin d) (Fin d) k).mulVec w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hc : ∀ g v, (↑P : Matrix (Fin d) (Fin d) k).mulVec ((↑(cj P ρ g) : Matrix (Fin d) (Fin d) k).mulVec v) =
      (↑(ρ g) : Matrix (Fin d) (Fin d) k).mulVec ((↑P : Matrix (Fin d) (Fin d) k).mulVec v) := by
    intro g v
    rw [cj_apply, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hPP]
  refine ⟨fun i g v hv => ?_, fun i U hU h1 h2 => ?_⟩
  · rw [hW', hc]
    exact hJH.1 i g _ ((hW' i v).1 hv)
  · let U0 : Submodule k (Fin d → k) := U.map (Matrix.mulVecLin (↑P : Matrix (Fin d) (Fin d) k))
    have hmem : ∀ v, v ∈ U ↔ (↑P : Matrix (Fin d) (Fin d) k).mulVec v ∈ U0 := by
      intro v
      constructor
      · intro hv
        exact ⟨v, hv, rfl⟩
      · rintro ⟨u, hu, he⟩
        have huv : u = v := by
          have := congrArg (fun w => (↑(P⁻¹) : Matrix (Fin d) (Fin d) k).mulVec w) he
          simpa [Matrix.mulVecLin_apply, hPP'] using this
        exact huv ▸ hu
    have hinv : IsInv ρ U0 := by
      rintro g w ⟨u, hu, rfl⟩
      refine ⟨(↑(cj P ρ g) : Matrix (Fin d) (Fin d) k).mulVec u, hU g u hu, ?_⟩
      simp only [Matrix.mulVecLin_apply]
      exact hc g u
    have hlo : W i ≤ U0 := by
      intro w hw
      refine ⟨(↑(P⁻¹) : Matrix (Fin d) (Fin d) k).mulVec w, h1 ((hW' i _).2 (by rw [hPP]; exact hw)), ?_⟩
      simp only [Matrix.mulVecLin_apply]
      exact hPP w
    have hhi : U0 ≤ W (i + 1) := by
      rintro w ⟨u, hu, rfl⟩
      exact (hW' (i + 1) u).1 (h2 hu)
    rcases hJH.2 i U0 hinv hlo hhi with h | h
    · left
      ext v
      rw [hmem, h, hW']
    · right
      ext v
      rw [hmem, h, hW']
end

section

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.matEx_of :
    MatEx := by
  intro Γ L _ _ M _ _ a h1 hmul U hU d b
  let f : Γ → (U →ₗ[L] U) := fun g => (a g).restrict (fun x hx => hU g x hx)
  have hfv : ∀ g (x : U), ((f g x : U) : M) = a g (x : M) := fun g x => rfl
  have hf1 : f 1 = LinearMap.id := by
    ext x
    simp [hfv, h1]
  have hfm : ∀ g h, f (g * h) = f g ∘ₗ f h := by
    intro g h
    ext x
    simp [hfv, hmul]
  let φ : Γ →* Matrix (Fin d) (Fin d) L :=
    { toFun := fun g => LinearMap.toMatrix b b (f g)
      map_one' := by
        simp only [hf1, LinearMap.toMatrix_id]
      map_mul' := by
        intro g h
        simp only [hfm]
        exact LinearMap.toMatrix_comp b b b (f g) (f h) }
  let ρ : Γ →* GL (Fin d) L := φ.toHomUnits
  have hρ : ∀ g, ((ρ g : GL (Fin d) L) : Matrix (Fin d) (Fin d) L) = LinearMap.toMatrix b b (f g) :=
    fun g => MonoidHom.coe_toHomUnits φ g
  refine ⟨ρ, ?_, ?_⟩
  · intro g j
    simp only [hρ, LinearMap.toMatrix_apply]
    rw [← hfv]
    have e := congrArg Subtype.val (b.sum_repr (f g (b j)))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at e
    exact e.symm
  · intro i j
    obtain ⟨μ, hμ⟩ := LinearMap.exists_extend (b.coord i)
    refine ⟨μ, fun g => ?_⟩
    rw [hρ, LinearMap.toMatrix_apply, ← hfv]
    have hc : μ (U.subtype (f g (b j))) = b.coord i (f g (b j)) := by
      rw [← LinearMap.comp_apply, hμ]
    rw [Module.Basis.coord_apply] at hc
    exact hc.symm
end

section

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

private theorem invariant_sup_alt {Γ k : Type} [Group Γ] [Field k] {d : ℕ} {ρ : Γ →* GL (Fin d) k}
    {U V : Submodule k (Fin d → k)} (hU : IsInv ρ U) (hV : IsInv ρ V) : IsInv ρ (U ⊔ V) := by
  intro g v hv
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
  rw [Matrix.mulVec_add]
  exact Submodule.add_mem_sup (hU g a ha) (hV g b hb)

private theorem invariant_inf {Γ k : Type} [Group Γ] [Field k] {d : ℕ} {ρ : Γ →* GL (Fin d) k}
    {U V : Submodule k (Fin d → k)} (hU : IsInv ρ U) (hV : IsInv ρ V) : IsInv ρ (U ⊓ V) := by
  intro g v hv
  exact ⟨hU g v hv.1, hV g v hv.2⟩

private theorem invariant_bot_alt {Γ k : Type} [Group Γ] [Field k] {d : ℕ} (ρ : Γ →* GL (Fin d) k) :
    IsInv ρ (⊥ : Submodule k (Fin d → k)) := by
  intro g v hv
  rw [(Submodule.mem_bot k).1 hv, Matrix.mulVec_zero]
  exact Submodule.zero_mem _

theorem UpperTheory.Gal.Int.Geo.sSOfSum_of :
    SSOfSum := by
  intro Γ k _ _ d ρ B hB hS hT W hW
  obtain ⟨W', ⟨hinv, hdis⟩, hmax⟩ :=
    (wellFounded_gt (α := Submodule k (Fin d → k))).has_min
      {X | IsInv ρ X ∧ Disjoint W X} ⟨⊥, invariant_bot_alt ρ, disjoint_bot_right⟩
  have key : ∀ i, B i ≤ W ⊔ W' := by
    intro i
    rcases hS i (B i ⊓ (W ⊔ W')) (invariant_inf (hB i) (invariant_sup_alt hW hinv)) inf_le_left with h | h
    · have hd : Disjoint W (W' ⊔ B i) := by
        rw [Submodule.disjoint_def]
        intro w hw hw2
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw2
        have h2 : (a + b) + -a ∈ W ⊔ W' := Submodule.add_mem_sup hw (neg_mem ha)
        have h3 : (a + b) + -a = b := by abel
        rw [h3] at h2
        have hbU : b ∈ B i ⊓ (W ⊔ W') := ⟨hb, h2⟩
        rw [h] at hbU
        have hb0 : b = 0 := (Submodule.mem_bot k).1 hbU
        subst hb0
        rw [add_zero] at hw ⊢
        exact Submodule.disjoint_def.1 hdis a hw ha
      have hle : W' ⊔ B i ≤ W' := by
        by_contra hn
        exact hmax _ ⟨invariant_sup_alt hinv (hB i), hd⟩
          (lt_of_le_not_ge le_sup_left hn)
      exact (le_sup_right.trans hle).trans le_sup_right
    · exact inf_eq_left.1 h
  refine ⟨W', hinv, hdis, codisjoint_iff.2 ?_⟩
  exact top_le_iff.1 (hT ▸ iSup_le key)
end

section

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

private theorem conj_basis {L : Type} [Field L] {M : Type*} [AddCommGroup M] [Module L M]
    (U : Submodule L M) {d : ℕ} (b : Module.Basis (Fin d) L U) (P : GL (Fin d) L) :
    ∃ b' : Module.Basis (Fin d) L U,
      ∀ j, (b' j).1 = ∑ i, (P : Matrix (Fin d) (Fin d) L) i j • (b i).1 := by
  have h1 : (P : Matrix (Fin d) (Fin d) L) * ((P⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : ((P⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L) * (P : Matrix (Fin d) (Fin d) L) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  let e : U ≃ₗ[L] U := LinearEquiv.ofLinear (Matrix.toLin b b (P : Matrix (Fin d) (Fin d) L))
    (Matrix.toLin b b ((P⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L))
    (by rw [← Matrix.toLin_mul b b b, h1, Matrix.toLin_one])
    (by rw [← Matrix.toLin_mul b b b, h2, Matrix.toLin_one])
  refine ⟨b.map e, fun j => ?_⟩
  have h : e (b j) = ∑ i, (P : Matrix (Fin d) (Fin d) L) i j • b i :=
    Matrix.toLin_self b b _ j
  simp [h]

private theorem conj_mat {L : Type} [Field L] {M : Type*} [AddCommGroup M] [Module L M]
    (f : M →ₗ[L] M) {d : ℕ} (x y : Fin d → M) (A P Q : Matrix (Fin d) (Fin d) L) (hPQ : P * Q = 1)
    (hx : ∀ j, f (x j) = ∑ i, A i j • x i) (hy : ∀ j, y j = ∑ i, P i j • x i) (j : Fin d) :
    f (y j) = ∑ i, (Q * A * P) i j • y i := by
  have key : ∀ (B : Matrix (Fin d) (Fin d) L) (j : Fin d),
      ∑ i, B i j • y i = ∑ t, (P * B) t j • x t := by
    intro B j
    simp only [hy, Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  rw [key, show P * (Q * A * P) = A * P by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPQ, Matrix.one_mul], hy j]

  simp only [map_sum, map_smul, hx, Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]

theorem UpperTheory.Gal.Int.Geo.matConj_of :
    MatConj := by
  intro l _ k _ H Ω _ _ L _ _ θ d ρ P ⟨b, hb⟩
  obtain ⟨b', hb'⟩ := conj_basis _ b P
  refine ⟨b', fun σ j => ?_⟩
  have h1 : (P : Matrix (Fin d) (Fin d) L) * ((P⁻¹ : GL (Fin d) L) : Matrix (Fin d) (Fin d) L) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [cj_apply, Units.val_mul, Units.val_mul]
  exact conj_mat (galV l H Ω L σ) (fun i => (b i).1) (fun i => (b' i).1) _ _ _ h1 (hb σ) hb' j
end

section

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

theorem UpperTheory.Gal.Int.Geo.totCont_of :
    GlobalTheory.GalV.VFin → DegCont → TotCont := by
  classical
  intro hVF hDC l _ k Ω _ _ _ _ hl X p hp v μ
  haveI := hp
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI : Algebra.IsAlgebraic k Ω := IsAlgClosure.isAlgebraic
  have hu : IsUnit (l : Ω) := by
    have h := (map_ne_zero (algebraMap k Ω)).mpr hl
    rw [map_natCast] at h
    exact h.isUnit
  have hfin : ∀ n : ℤ, Module.Finite ℤ_[l] (Hl l (sch.obj (geom Ω p)) n 0) := fun n =>
    (hVF l Ω hu (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))) n 0).1
  have hv : ∀ σ, μ (galTot l Ω p σ v) = ∑ n ∈ v.support,
      (μ ∘ₗ DirectSum.lof ℚ_[l] ℤ (fun n => HQ l (sch.obj (geom Ω p)) n 0) n)
        (galHQ l Ω p n 0 σ (v n)) := by
    intro σ
    conv_lhs => rw [← DirectSum.sum_support_of v]

    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [LinearMap.comp_apply]
    congr 1
    exact DirectSum.lmap_lof (fun n => galHQ l Ω p n 0 σ) n (v n)
  simp_rw [hv]
  exact continuous_finsetSum _ fun n _ => hDC l k Ω p inferInstance inferInstance n 0 (hfin n) (v n) _
end
