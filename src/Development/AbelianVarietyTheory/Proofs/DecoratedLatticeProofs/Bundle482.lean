module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle258
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemAdelicLatticeIffLocalSelfDualCompletion
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle145
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle472
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle164
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle184
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle166
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClopenIsCompactQLat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairOperatorStatement
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle377
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle471
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle406
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle410
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle474
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle425
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle473
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.MovesPl

open GlobalTheory.FinPl GlobalTheory.FinPl.KSplit GlobalTheory.FinPl.KOpen

variable {D : D7}

theorem latV_transfer (S : HSp D) (L : Lat S) {P₁ P₂ : Pl D → Prop} (h : ∀ p, P₁ p → P₂ p)
    {z : Fin S.rank → AE D} (hz : ∀ i, z i ∈ idAt D P₁) : z ∈ latV S L P₁ ↔ z ∈ latV S L P₂ := by
  rw [mem_latV_iff S L P₁ z hz, mem_latV_iff S L P₂ z fun i => idAt_mono h (hz i)]

theorem mem_latV_empty (S : HSp D) (L : Lat S) {z : Fin S.rank → AE D}
    (hz : ∀ i, z i ∈ idAt D (· ∈ (∅ : Finset (Pl D)))) : z ∈ latV S L (· ∈ (∅ : Finset (Pl D))) := by
  classical
  rw [mem_latV_iff S L _ z hz]
  have h0 : finPart D ∘ z = 0 := by
    funext i
    rw [Function.comp_apply, ← e_mul_fin (hz i)]
    refine GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun w => ?_
    change GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w _ = GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w _
    rw [map_mul, compFin_e, if_neg (Finset.notMem_empty w), zero_mul, Pi.zero_apply, map_zero]
  rw [h0]
  exact zero_mem _

theorem moves_of_places : ∀ {D : D7} (S : HSp D) (g : GA D S) (L M : Lat S) (Q : Finset (Pl D)),
    (∀ v ∈ Q, Moves S g L M (· = v)) → Moves S g L M (· ∈ Q) := by
  intro D S g L M Q
  classical
  induction Q using Finset.induction_on with
  | empty =>
    intro _ y hy
    exact iff_of_true (mem_latV_empty S L hy) (mem_latV_empty S M (supp_mulVec S _ g hy))
  | insert v Q hv ih =>
    intro hQ y hy
    have hQ' := ih fun w hw => hQ w (Finset.mem_insert_of_mem hw)
    have hvv := hQ v (Finset.mem_insert_self v Q)
    have hgy := supp_mulVec S _ g hy
    have comm : ∀ c : AE D, c • (mt S g *ᵥ y) = mt S g *ᵥ (c • y) := fun c => (mulVec_smul _ _ _).symm
    have s1 : ∀ i, (eQ {v} • y) i ∈ idAt D (fun p => p ∈ insert v Q ∧ p ∈ ({v} : Finset (Pl D))) :=
      fun i => mul_mem_idAt (eQ_off {v}) (hy i)
    have s2 : ∀ i, ((1 - eQ {v}) • y) i ∈ idAt D (fun p => p ∈ insert v Q ∧ p ∉ ({v} : Finset (Pl D))) :=
      fun i => mul_mem_idAt (one_sub_eQ_off {v}) (hy i)
    have i1 : ∀ p, (p ∈ insert v Q ∧ p ∈ ({v} : Finset (Pl D))) → p = v := fun p h => Finset.mem_singleton.1 h.2
    have i2 : ∀ p, (p ∈ insert v Q ∧ p ∉ ({v} : Finset (Pl D))) → p ∈ Q := fun p h =>
      (Finset.mem_insert.1 h.1).resolve_left fun e => h.2 (Finset.mem_singleton.2 e)
    have t1 : ∀ i, (eQ {v} • y) i ∈ idAt D (· = v) := fun i => idAt_mono i1 (s1 i)
    have t2 : ∀ i, ((1 - eQ {v}) • y) i ∈ idAt D (· ∈ Q) := fun i => idAt_mono i2 (s2 i)
    rw [mem_latV_iff_parts S L _ {v} hy, mem_latV_iff_parts S M _ {v} hgy, comm, comm,
      latV_transfer S L i1 s1, latV_transfer S L i2 s2,
      latV_transfer S M i1 (fun i => by rw [← comm]; exact mul_mem_idAt (eQ_off {v}) (hgy i)),
      latV_transfer S M i2 (fun i => by rw [← comm]; exact mul_mem_idAt (one_sub_eQ_off {v}) (hgy i))]
    exact and_congr (hvv _ t1) (hQ' _ t2)

end GlobalTheory.FinPl.MovesPl

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SrcGl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem tensCol_mul_blk (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ) (g : GL n' k) (x : Matrix n (n' ⊕ Fin 1) k) :
    tensCol Ψ a (x * (blk g).val) = tensCol (fun x₀ => Ψ (x₀ * g.val)) a x := by
  simp only [tensCol, blk_val]
  congr 2
  · ext i j
    simp [Matrix.mul_apply, fromBlocks, Fintype.sum_sum_type]
  · ext i
    simp [Matrix.mul_apply, fromBlocks, Fintype.sum_sum_type]

theorem phiOne_smul_left (g : GL n' k) (P : Pair k n') (Q : Pair k n) (x : Matrix n n' k) :
    phiOne (g • P) Q x = phiOne P Q (x * g.val) := by
  classical
  have hs : ∀ (h : GL n' k) (y : n' → k), h • y = h.val *ᵥ y := fun _ _ => rfl
  unfold phiOne
  congr 1
  apply propext
  rw [maps_iff_hasVal, maps_iff_hasVal]
  constructor
  · intro h y a hy
    have := h (g • y) a (hy.gl_smul g)
    simpa [hs, Matrix.mulVec_mulVec] using this
  · intro h y a hy
    have := h (g⁻¹ • y) a (Pair.smul_hasVal.1 hy)
    simpa [hs, Matrix.mulVec_mulVec] using this

end GlobalTheory.FinPl.SrcGl

namespace GlobalTheory.FinPl.SrcGl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {n' : Type} [Fintype n'] [DecidableEq n']

theorem coe_FFStar {A : HSp D} (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (φ : Form k n' (CA A)) (P : Pair k n') :
    ((FFStar q χ φ P : CA A) : GA D A → ℂ) = FFStar q χ (fun P => (φ P : GA D A → ℂ)) P := by
  simp [FFStar_apply]

def toCA {A : HSp D} (φ : Form k n' (GA D A → ℂ)) (h : ∀ P, IsContAut A (φ P)) : Form k n' (CA A) :=
  fun P => ⟨φ P, h P⟩

theorem toCA_ram {A : HSp D} {α : Frame p A n'} {φ : Form k n' (GA D A → ℂ)} (hφ : IsRam α φ) :
    toCA φ hφ.2.2 ∈ Mram k n' (CA A) ∧ toCA φ hφ.2.2 ∈ EqForm (caRep α) := by
  letI := Fintype.ofFinite 𝓀[k]ˣ
  refine ⟨(mem_Mram _).2 fun P => Subtype.ext ?_, fun g P => Subtype.ext (hφ.1 g P)⟩
  simpa [toCA] using (mem_Mram φ).1 hφ.2.1 P

theorem exists_lat_eq (P : Pair k n') : ∃ P' : Pair k n', P'.lat = P.ker := by
  have h1 : Module.finrank 𝓀[k] (Red P.ker) = Module.finrank 𝓀[k] (Red P.lat) := by
    rw [Red.finrank_eq, Red.finrank_eq]
  have h2 : Nontrivial (Red P.lat) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact P.red_ne (LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero])
  have h3 : 0 < Module.finrank 𝓀[k] (Red P.ker) := h1 ▸ Module.finrank_pos
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.1 h3
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual 𝓀[k] (Red P.ker), f x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx ((Module.forall_dual_apply_eq_zero_iff 𝓀[k] x).1 h)
  exact ⟨ofDual P.ker ⟨f, fun h0 => hf (by rw [h0]; rfl)⟩, ofDual_lat _ _⟩

variable {n : Type} [Fintype n] [DecidableEq n]

def tensL (a : (n → k) → ℂ) : (Matrix n n' k → ℂ) →ₗ[ℂ] (Matrix n (n' ⊕ Fin 1) k → ℂ) where
  toFun Ψ := tensCol Ψ a
  map_add' Ψ Ψ' := by ext x; simp [tensCol, add_mul]
  map_smul' c Ψ := by ext x; simp [tensCol, mul_assoc]

@[simp] theorem tensL_apply (a : (n → k) → ℂ) (Ψ : Matrix n n' k → ℂ) : tensL a Ψ = tensCol Ψ a := rfl

theorem tensCol_add (Ψ Ψ' : Matrix n n' k → ℂ) (a : (n → k) → ℂ) : tensCol (Ψ + Ψ') a = tensCol Ψ a + tensCol Ψ' a :=
  (tensL a).map_add Ψ Ψ'

end GlobalTheory.FinPl.SrcGl

open GlobalTheory.FinPl GlobalTheory.FinPl.SrcGl in
theorem GlobalTheory.FinPl.sourceGlued : ∀ D : D7, GlobalTheory.FinPl.SourceGlued D := by
  intro D k _ _ _ _ p n n' _ _ _ _ q χ₀ hχ χ hχχ ψ S A L T o ζ hL hA vA χS χT om hW _ hT α α₀ β hsum P P₁ Λ _
  obtain ⟨lS, hlS, hθ⟩ := GlobalTheory.T.exists_bilinear_equivariant_orthogonalSummandLift D k p n n' ψ S A L T o ζ hL hA vA χS χT om hW α α₀ β hsum
  have hdet : ∀ L' : Submodule 𝒪[k] (n' → k), L'.IsFullLattice k → ∀ g ∈ latStab L',
      ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) = 1 := fun L' hL' g hg => by
    rw [GlobalTheory.T.unramifiedCharacter_det_latticeStabilizer_eq_one k n' L' hL' g hg lS (hlS hT), Units.val_one]
  have hsb := GlobalTheory.T.schwartzBruhat_tensor_indicator_character_facts k n n'

  have hinv : ∀ (θ : CA A →ₗ[ℂ] (Matrix n (n' ⊕ Fin 1) k → ℂ) →ₗ[ℂ] (GA D T → WO L T → ℂ)),
      (∀ (g : GL n' k) (v : CA A) (Φ : Matrix n (n' ⊕ Fin 1) k → ℂ), Φ ∈ SB (Matrix n (n' ⊕ Fin 1) k) →
        θ (caRep α g v) (fun x => Φ (x * (blk g).val)) = ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ • θ v Φ) →
      ∀ a ∈ SB (n → k), ∀ L' : Submodule 𝒪[k] (n' → k), L'.IsFullLattice k →
        GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.IsLiftInv (caRep α) (θ.compl₂ (tensL a)) L' := by
    intro θ hθe a ha L' hL' g hg v Ψ hΨ
    simp only [LinearMap.compl₂_apply, tensL_apply]
    have := hθe g v _ (hsb.1 Ψ a hΨ ha)
    rw [hdet L' hL' g hg, inv_one, one_smul] at this
    refine Eq.trans (congrArg _ ?_) this
    funext x
    exact (tensCol_mul_blk Ψ a g x).symm
  obtain ⟨P', hP'⟩ := exists_lat_eq P
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (GL n' k) P' P₁
  refine ⟨⟨((resCard k : ℂ) ^ Fintype.card n)⁻¹ * ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ), ?_⟩, ?_⟩
  · intro LS LT f₀ Ξ Ξ' hΞ hΞ' φ hφ
    obtain ⟨θ, hθv, hθe⟩ := hθ LS LT f₀ hΞ.1 hΞ.2.1 hΞ.2.2.1
    obtain ⟨hram, heq⟩ := toCA_ram hφ
    set φc := toCA φ hφ.2.2 with hφc
    have hχ1 : χ ≠ 1 := hχχ ▸ resChar_ne_one hχ q
    rw [show liftA o om vA (φ P) Ξ = θ (φc P) _ from (hθv (φc P) _ _ hΞ).symm,
      ((GlobalTheory.T.gluedLattice_finite_expansions_localField k n n' q χ hχ1 Λ).1 P).1]
    have e0 : θ (φc P) (tensCol (latInd P.ker Λ) (vecInd Λ)) = 0 :=
      GlobalTheory.LastSteps.lift_latInd P hram heq (hinv θ hθe _ (hsb.2.1 Λ inferInstance) P.ker inferInstance) Λ
    have e1 : ∀ Q ∈ withLat Λ, θ (φc P) (tensCol (latInd P.ker Q.ker + GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData.mainDatum q χ 1 P Q)
        (charInd χ Q)) = ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) • liftA o om vA (FFStar q χ φ P₁) (Ξ' Q) := by
      intro Q hQ
      have hI := hinv θ hθe _ (hsb.2.2 χ Q) P.ker inferInstance
      have a0 : θ (φc P) (tensCol (latInd P.ker Q.ker) (charInd χ Q)) = 0 :=
        GlobalTheory.LastSteps.lift_latInd P hram heq hI Q.ker
      have a1 := GlobalTheory.LastSteps.lift_mainDatum q χ 1 heq hI Q rfl hP'
      simp only [LinearMap.compl₂_apply, tensL_apply, map_one, Module.End.one_apply] at a1
      have a2 := hθe g⁻¹ (FFStar q χ φc P₁) _ (hΞ' Q hQ).2.2.2.1
      have b1 : caRep α g⁻¹ (FFStar q χ φc P₁) = FFStar q χ φc P' := by
        rw [← hg, FFStar_mem_EqForm q χ heq g P', ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          Module.End.one_apply]
      have b2 : (fun x => tensCol (phiOne P₁ Q) (charInd χ Q) (x * (blk g⁻¹).val)) = tensCol (phiOne P' Q) (charInd χ Q) := by
        funext x
        rw [tensCol_mul_blk]
        congr 1
        funext x₀
        rw [← hg, phiOne_smul_left, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      rw [b1, b2, hθv _ _ _ (hΞ' Q hQ), coe_FFStar] at a2
      rw [tensCol_add, map_add (f := _), a0, zero_add, a1, a2, map_inv, map_inv, Units.val_inv_eq_inv_val, inv_inv]
      rfl

    rw [map_smul, map_add (f := _), map_sum, e0, zero_add, Finset.sum_congr rfl e1, ← Finset.smul_sum, smul_smul]
  · intro LS LT f₀ Ξ a hor φ hφ
    obtain ⟨L₁, hL₁, hO⟩ : ∃ L₁ : Submodule 𝒪[k] (n' → k), (L₁ = P.lat ∨ L₁ = P.ker) ∧
        Over ψ α₀ β LS LT f₀ (tensCol (latInd L₁ Λ) a) Ξ := by
      rcases hor with h | h
      exacts [⟨_, Or.inl rfl, h⟩, ⟨_, Or.inr rfl, h⟩]
    haveI : L₁.IsFullLattice k := by rcases hL₁ with rfl | rfl <;> infer_instance
    obtain ⟨θ, hθv, hθe⟩ := hθ LS LT f₀ hO.1 hO.2.1 hO.2.2.1
    obtain ⟨hram, heq⟩ := toCA_ram hφ
    set φc := toCA φ hφ.2.2 with hφc
    rw [show liftA o om vA (φ P) Ξ = θ (φc P) _ from (hθv (φc P) _ _ hO).symm]
    have hinvL : ∀ g ∈ latStab L₁, ∀ w, θ (caRep α g w) (tensCol (latInd L₁ Λ) a) = θ w (tensCol (latInd L₁ Λ) a) := by
      intro g hg w
      have := hθe g w _ hO.2.2.2.1
      rw [hdet L₁ inferInstance g hg, inv_one, one_smul] at this
      refine Eq.trans (congrArg _ ?_) this
      funext x
      rw [tensCol_mul_blk]
      congr 1
      funext x₀
      exact (GlobalTheory.LastSteps.latInd_mul hg Λ x₀).symm
    have hv : formOf (caRep α) P (evalEquiv (caRep α) P ⟨φc, heq⟩) = φc :=
      congrArg Subtype.val ((evalEquiv (caRep α) P).left_inv ⟨φc, heq⟩)
    exact (GlobalTheory.PairOp.vanishing q).invariant_eq_zero (caRep α) P (evalEquiv (caRep α) P ⟨φc, heq⟩) (hv.symm ▸ hram) _
      (θ.flip (tensCol (latInd L₁ Λ) a)) (by
        rcases hL₁ with rfl | rfl
        exacts [Or.inl fun g hg w => hinvL g hg w, Or.inr fun g hg w => hinvL g hg w])
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section



namespace GlobalTheory.FinPl.ScalarDual

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

open GlobalTheory.FinPl.FrameLat

theorem idAt_mono {P Q : Pl D → Prop} (hPQ : ∀ w, P w → Q w) {a : AE D} (ha : a ∈ idAt D P) : a ∈ idAt D Q := by
  unfold idAt at ha ⊢
  obtain ⟨h0, hw⟩ := Ideal.mem_inf.1 ha
  exact Ideal.mem_inf.2 ⟨h0, (Submodule.mem_iInf _).2 fun w =>
    (Submodule.mem_iInf _).1 hw ⟨w.1, fun hp => w.2 (hPQ _ hp)⟩⟩

theorem pr_eq_zero (q : SplitPt D k) {w : Pl D} (hw : w ≠ q.v) {a : AE D} (ha : a ∈ idAt D (· = w)) : q.pr a = 0 := by
  have h1 : q.e * a ∈ idAt D (· = w) := Ideal.mul_mem_left _ _ ha
  have h2 : q.e * a ∈ idAt D (· = q.v) := Ideal.mul_mem_right _ _ (e_mem_idAt q)
  unfold idAt at h1 h2
  have h0 : q.e * a = 0 := by
    apply GlobalTheory.FinPlLoc.eq_zero_of_comp
    · exact RingHom.mem_ker.1 (Ideal.mem_inf.1 h1).1
    · intro u
      by_cases hu : u = w
      · subst hu
        exact RingHom.mem_ker.1 ((Submodule.mem_iInf _).1 (Ideal.mem_inf.1 h2).2 ⟨u, hw⟩)
      · exact RingHom.mem_ker.1 ((Submodule.mem_iInf _).1 (Ideal.mem_inf.1 h1).2 ⟨u, hu⟩)
  rw [← q.pr_sec (q.pr a), q.sec_pr, h0, map_zero]

theorem pr_cA_xi_int (q : SplitPt D k) (hU : q.UnitAA) :
    q.pr (cA D (incA D D.host.xi0)) ∈ 𝒪[k] ∧ q.pr (cA D (incA D D.host.xi0⁻¹)) ∈ 𝒪[k] := by
  have hid : cA D (q.sec 1) ∈ idAt D (· = q.v) := csec_mem_idAt (p := q) 1
  have hc : cA D (q.sec 1) ∈ intAt D (· = q.v) := by
    refine (GlobalTheory.SplitIntComp.mem_intAt_iff q hid).2 ⟨?_, ?_⟩
    · rw [GlobalTheory.SplitLineSim.pr_cA_sec]; exact zero_mem _
    · rw [Formalism.L2.Theta.cA_cA, q.pr_sec]; exact one_mem _
  have h2 := hU.1 _ hc
  have a1 := ((GlobalTheory.SplitIntComp.mem_intAt_iff q h2.1.1).1 h2.1).2
  have a2 := ((GlobalTheory.SplitIntComp.mem_intAt_iff q h2.2.1).1 h2.2).2
  rw [map_mul, Formalism.L2.Theta.cA_cA, map_mul, q.pr_sec, mul_one] at a1 a2
  exact ⟨a1, a2⟩

theorem cond_dual : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (P : Pl D → Prop), Places p I P → ∀ (h h' : D.host.E), h ≠ 0 → h' ≠ 0 → star h' = h' → h = D.host.xi0 * star D.host.xi0 * h' → ∀ d : AE D, d ∈ idAt D P → ((∀ i, (p i).pr d ∈ 𝒪[k] ∧ (p i).pr (cA D d) * (p i).pr (incA D h') ∈ 𝒪[k]) ↔ ∀ c : AE D, c ∈ idAt D P → (∀ i, (p i).pr c ∈ 𝒪[k] ∧ (p i).pr (cA D c) * (p i).pr (incA D h) ∈ 𝒪[k]) → incA D (D.host.xi0⁻¹) * cA D d * c * incA D h ∈ intAt D P) := by
  intro D k _ _ _ _ ι p I P hP h h' hh hh' hs hhe d hd
  have hne : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hv : ∀ i, P (p i).v := fun i => (hP.mem _).2 ⟨i, rfl⟩
  have hne_v : ∀ i j, i ≠ j → (p i).v ≠ (p j).v := fun i j hij e => hij (hP.inj e)
  have hU := fun i => pr_cA_xi_int (p i) (hP.unit i)
  have hprod : ∀ i, (p i).pr (cA D (incA D D.host.xi0⁻¹)) * (p i).pr (cA D (incA D D.host.xi0)) = 1 := by
    intro i
    rw [← map_mul, ← map_mul, ← map_mul, inv_mul_cancel₀ hne, map_one, map_one, map_one]
  have hch : cA D (incA D h) = incA D h := by
    rw [cA_incA, hhe, star_mul, star_mul, star_star, hs]
    ring_nf
  have hx1 : incA D D.host.xi0⁻¹ * incA D h = cA D (incA D D.host.xi0) * incA D h' := by
    rw [cA_incA, ← map_mul, ← map_mul, hhe, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hX : ∀ c, incA D D.host.xi0⁻¹ * cA D d * c * incA D h =
      cA D (incA D D.host.xi0) * (cA D d * incA D h') * c := fun c => by
    linear_combination (cA D d * c) * hx1
  have hcX : ∀ c, cA D (incA D D.host.xi0⁻¹ * cA D d * c * incA D h) =
      cA D (incA D D.host.xi0⁻¹) * d * (cA D c * incA D h) := fun c => by
    simp only [map_mul, Formalism.L2.Theta.cA_cA, hch]
    ring
  constructor
  · intro hdc c hc hcc
    refine (GlobalTheory.T.mem_integralAdeles_splitPlaces_iff_halves D k ι p I P hP _).2 ⟨Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hc), fun i => ⟨?_, ?_⟩⟩
    · rw [hX, map_mul (p i).pr, map_mul (p i).pr, map_mul (p i).pr]
      exact mul_mem (mul_mem (hU i).1 (hdc i).2) (hcc i).1
    · rw [hcX, map_mul (p i).pr, map_mul (p i).pr, map_mul (p i).pr]
      exact mul_mem (mul_mem (hU i).2 (hdc i).1) (hcc i).2
  · intro H i
    have hsup : ∀ {a : AE D}, a ∈ idAt D (· = (p i).v) → a ∈ idAt D P :=
      fun ha => idAt_mono (fun w hw => by rw [hw]; exact hv i) ha

    have hcond1 : ∀ j, (p j).pr ((p i).sec 1) ∈ 𝒪[k] ∧
        (p j).pr (cA D ((p i).sec 1)) * (p j).pr (incA D h) ∈ 𝒪[k] := by
      intro j
      by_cases hij : j = i
      · subst hij
        rw [(p j).pr_sec, GlobalTheory.SplitLineSim.pr_cA_sec, zero_mul]
        exact ⟨one_mem _, zero_mem _⟩
      · rw [pr_eq_zero (p j) (hne_v i j (Ne.symm hij)) (sec_mem_idAt (p i) 1),
          pr_eq_zero (p j) (hne_v i j (Ne.symm hij)) (csec_mem_idAt (p := p i) 1), zero_mul]
        exact ⟨zero_mem _, zero_mem _⟩
    have h1 := (((GlobalTheory.T.mem_integralAdeles_splitPlaces_iff_halves D k ι p I P hP _).1 (H _ (hsup (sec_mem_idAt (p i) 1)) hcond1)).2 i).1
    rw [hX, map_mul (p i).pr, map_mul (p i).pr, map_mul (p i).pr, (p i).pr_sec, mul_one] at h1

    have hh0 : (p i).pr (incA D h) ≠ 0 := by
      intro h0
      have := congrArg (p i).pr (congrArg (incA D) (mul_inv_cancel₀ hh))
      rw [map_mul (incA D), map_mul (p i).pr, h0, zero_mul, map_one, map_one] at this
      exact zero_ne_one this
    have hcond2 : ∀ j, (p j).pr (cA D ((p i).sec ((p i).pr (incA D h))⁻¹)) ∈ 𝒪[k] ∧
        (p j).pr (cA D (cA D ((p i).sec ((p i).pr (incA D h))⁻¹))) * (p j).pr (incA D h) ∈ 𝒪[k] := by
      intro j
      rw [Formalism.L2.Theta.cA_cA]
      by_cases hij : j = i
      · subst hij
        rw [GlobalTheory.SplitLineSim.pr_cA_sec, (p j).pr_sec, inv_mul_cancel₀ hh0]
        exact ⟨zero_mem _, one_mem _⟩
      · rw [pr_eq_zero (p j) (hne_v i j (Ne.symm hij)) (sec_mem_idAt (p i) ((p i).pr (incA D h))⁻¹),
          pr_eq_zero (p j) (hne_v i j (Ne.symm hij)) (csec_mem_idAt (p := p i) ((p i).pr (incA D h))⁻¹), zero_mul]
        exact ⟨zero_mem _, zero_mem _⟩
    have h2 := (((GlobalTheory.T.mem_integralAdeles_splitPlaces_iff_halves D k ι p I P hP _).1 (H _ (hsup (csec_mem_idAt (p := p i) ((p i).pr (incA D h))⁻¹)) hcond2)).2 i).2
    rw [hcX, Formalism.L2.Theta.cA_cA] at h2
    have e3 : (p i).pr (cA D (incA D D.host.xi0⁻¹) * d * ((p i).sec ((p i).pr (incA D h))⁻¹ * incA D h)) =
        (p i).pr (cA D (incA D D.host.xi0⁻¹)) * (p i).pr d := by
      simp only [map_mul, (p i).pr_sec]
      rw [inv_mul_cancel₀ hh0, mul_one]
    rw [e3] at h2
    refine ⟨?_, ?_⟩
    · have e2 : (p i).pr d = (p i).pr (cA D (incA D D.host.xi0)) *
          ((p i).pr (cA D (incA D D.host.xi0⁻¹)) * (p i).pr d) := by
        linear_combination (-(p i).pr d) * hprod i
      rw [e2]; exact mul_mem (hU i).1 h2
    · have e1 : (p i).pr (cA D d) * (p i).pr (incA D h') = (p i).pr (cA D (incA D D.host.xi0⁻¹)) *
          ((p i).pr (cA D (incA D D.host.xi0)) * ((p i).pr (cA D d) * (p i).pr (incA D h'))) := by
        linear_combination (-((p i).pr (cA D d) * (p i).pr (incA D h'))) * hprod i
      rw [e1]; exact mul_mem (hU i).2 h1

end GlobalTheory.FinPl.ScalarDual

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

theorem _root_.GlobalTheory.T.lattices_same_splitShape_carried_by_central : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S S₀ A Ln : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A Ln) (ζ : Fin Ln.rank → D.host.E) (L L' : Lat S) (N N' : Lat A) (α α' β β' : Fin ρ → k) (γ δ c₀ : k) (a₀ : GA D A), IsLineVec Ln ζ → IsSelfDualC S L → IsSelfDualC S L' → WShape p d o ζ L α α' γ 1 N → WShape p d o ζ L' β β' δ a₀ N' → latV A N (· = p.v) = latV A N' (· = p.v) → c₀ ≠ 0 → (∀ i, valuation k (β i * c₀) = valuation k (α i)) → (∀ i, valuation k (β' i * c₀) = valuation k (α' i)) → valuation k (δ * c₀) = valuation k γ → ∃ (a : GA D A) (c : AE D), CenAt A p.v a ∧ NormOneAt p.v c ∧ SMoves S c (embA d o (a₀ * a)) L L' p.v := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.sMoves_of_wShape | exact GlobalTheory.Core.Mi.LatMatch.sMoves_of_wShape | (intros; apply GlobalTheory.Core.Mi.LatMatch.sMoves_of_wShape <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

theorem _root_.GlobalTheory.T.orthogonalSumCores_homothetic_off_level : ∀ (D : D7) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M M' : Lat S) (LA : Lat A) (LL : Lat L) (μ : D.host.E) (T : ℕ) (v : GlobalTheory.FinPl.Pl D) (a₀ : GA D A), IsLineVec L ζ → IsSelfDualC L LL → OrthAt o M LA LL v → TraceAt o a₀ LA M' v → SplitsAt o M' v → μ ≠ 0 → LineAt (vecB o ζ) μ M' v → star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E)) → (T : 𝓞 D.host.F) ∉ v.asIdeal → ∃ (a : GA D A) (c : AE D), CenAt A v a ∧ NormOneAt v c ∧ SMoves S c (o.emb (a₀ * a, 1)) M M' v := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.coreOff_homothetic | exact GlobalTheory.Core.Mi.LatMatch.coreOff_homothetic | (intros; apply GlobalTheory.Core.Mi.LatMatch.coreOff_homothetic <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

theorem _root_.GlobalTheory.T.orthogonalEmbedding_keeps_gluedCore_iff_fixes_pair : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p A n) (β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)) (M : Lat S) (q : GlobalTheory.LatPair.Unif k) (m : k) (P : GlobalTheory.LatPair.Pair k n), IsSumFrame o ζ β β₀ → IsSelfDualC S M → m ≠ 0 → GluedW β₀ M q m P → ∀ g : GL n k, Moves S (o.emb (β.gl g, 1)) M M (· = p.v) ↔ g • P = P := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.moves_emb_iff_smul_eq | exact GlobalTheory.Core.Mi.LatMatch.moves_emb_iff_smul_eq | (intros; apply GlobalTheory.Core.Mi.LatMatch.moves_emb_iff_smul_eq <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.local_component_measure_equation : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ (N₁ : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M₁ : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N₁ j)) → (∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N₁ j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M₁ j ρ h)) → (∀ PP hP j ρ h (hj : j ≤ (l PP hP).s + 1) (F₀ : Frame (l PP hP).k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit (l PP hP).q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc PP hP j) ((l PP hP).FX j hj) F₀ → IntIn (l PP hP).q _ F₀ (M₁ j ρ h)) → ∀ PP (hP : PP ∈ (pk W).Pg ∨ QAll W PP), SplitAt { v with N := N₁ } { o with M := M₁ } ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  first | exact @GlobalTheory.SplitAtPlaces.splitAt_places | exact GlobalTheory.SplitAtPlaces.splitAt_places | (intros; apply GlobalTheory.SplitAtPlaces.splitAt_places <;> assumption)
end
