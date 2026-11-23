module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle149
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle024
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle190
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle403
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle213
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle406
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle231
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle153
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardTorsionMulFinrank
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle155
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle088
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle072
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachDeltaInvariantCoboundaries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle346
public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle407
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil Matrix

namespace GlobalTheory.IndField

variable {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

section Gen

variable {K₁ K₂ : Type} [Field K₁] [ValuativeRel K₁] [TopologicalSpace K₁] [IsNonarchimedeanLocalField K₁]
  [Field K₂] [ValuativeRel K₂] [TopologicalSpace K₂] [IsNonarchimedeanLocalField K₂]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def pullFun (e : (Σ a, m a) ≃ n) {ρ₁ : Representation ℂ (Levi K₁ m) W}
    {ρ₂ : Representation ℂ (Levi K₂ m) W}
    (s : GL n K₂ →* GL n K₁) (hs : Continuous s) (t : Levi K₂ m →* Levi K₁ m)
    (hP : ∀ p : parab K₂ e, s p ∈ parab K₁ e)
    (hL : ∀ p : parab K₂ e, leviProj K₁ e ⟨s p, hP p⟩ = t (leviProj K₂ e p))
    (hρ : ∀ L, ρ₂ L = ρ₁ (t L)) (hδ : ∀ L, deltaHalf K₁ m (t L) = deltaHalf K₂ m L) :
    IndSp e ρ₁ →ₗ[ℂ] IndSp e ρ₂ where
  toFun f := ⟨⟨fun x => f.1.1 (s x), fun p g => by
      show f.1.1 (s ((p : GL n K₂) * g)) =
        (deltaHalf K₂ m (leviProj K₂ e p) : ℂ) • ρ₂ (leviProj K₂ e p) (f.1.1 (s g))
      rw [map_mul, parInd_law e ρ₁ f ⟨s p, hP p⟩ (s g), hL, hδ, hρ]⟩, by
      apply mem_smoothPart_of_nhds
      have h1 : s ⁻¹' {g | ind (parab K₁ e) ((twist ρ₁ (deltaHalf K₁ m)).comp (leviProj K₁ e)) g f.1 = f.1}
          ∈ nhds (1 : GL n K₂) :=
        (f.2.preimage hs).mem_nhds (by simp)
      refine Filter.mem_of_superset h1 fun x hx => ?_
      refine Subtype.ext (funext fun y => ?_)
      show f.1.1 (s (y * x)) = f.1.1 (s y)
      rw [map_mul]
      exact congrArg (fun v : indSpace (parab K₁ e) ((twist ρ₁ (deltaHalf K₁ m)).comp (leviProj K₁ e)) =>
        (v : GL n K₁ → W) (s y)) hx⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Gen

section Gen2

variable {K₁ K₂ : Type} [Field K₁] [ValuativeRel K₁] [TopologicalSpace K₁] [IsNonarchimedeanLocalField K₁]
  [Field K₂] [ValuativeRel K₂] [TopologicalSpace K₂] [IsNonarchimedeanLocalField K₂]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def pullMap (e : (Σ a, m a) ≃ n) {ρ₁ : Representation ℂ (Levi K₁ m) W}
    {ρ₂ : Representation ℂ (Levi K₂ m) W}
    (s : GL n K₂ →* GL n K₁) (hs : Continuous s) (t : Levi K₂ m →* Levi K₁ m)
    (hP : ∀ p : parab K₂ e, s p ∈ parab K₁ e)
    (hL : ∀ p : parab K₂ e, leviProj K₁ e ⟨s p, hP p⟩ = t (leviProj K₂ e p))
    (hρ : ∀ L, ρ₂ L = ρ₁ (t L)) (hδ : ∀ L, deltaHalf K₁ m (t L) = deltaHalf K₂ m L) :
    Representation.IntertwiningMap ((parInd e ρ₁).comp s) (parInd e ρ₂) :=
  ⟨pullFun e s hs t hP hL hρ hδ, fun g => LinearMap.ext fun f =>
    Subtype.ext (Subtype.ext (funext fun x => by
      show f.1.1 (s x * s g) = f.1.1 (s (x * g))
      rw [map_mul]))⟩

end Gen2

section Map

variable {R S : Type} [CommRing R] [CommRing S]

def blockMap (φ : R →+* S) : Levi R m →* Levi S m :=
  MonoidHom.pi fun a => (GeneralLinearGroup.map φ).comp (Pi.evalMonoidHom (fun a => GL (m a) R) a)

@[simp] theorem blockMap_apply (φ : R →+* S) (L : Levi R m) (a : α) :
    blockMap φ L a = GeneralLinearGroup.map φ (L a) := rfl


omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] in
theorem map_mem_parab (e : (Σ a, m a) ≃ n) (φ : R →+* S) (p : parab R e) :
    GeneralLinearGroup.map φ (p : GL n R) ∈ parab S e :=
  mem_parab.2 fun i j h => by
    change φ (((p : GL n R) : Matrix n n R) i j) = 0
    rw [mem_parab.1 p.2 i j h, map_zero]

theorem leviProj_map (e : (Σ a, m a) ≃ n) (φ : R →+* S) (p : parab R e) :
    leviProj S e ⟨GeneralLinearGroup.map φ (p : GL n R), map_mem_parab e φ p⟩ =
      blockMap φ (leviProj R e p) :=
  funext fun _ => Matrix.GeneralLinearGroup.ext fun _ _ => rfl

theorem continuous_glMap [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace S] [IsTopologicalRing S]
    (φ : R →+* S) (hφ : Continuous φ) : Continuous (GeneralLinearGroup.map (n := n) φ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (Units.continuous_val.matrix_map hφ : Continuous fun g : GL n R => (g : Matrix n n R).map φ)
  · have : (fun g : GL n R => (((GeneralLinearGroup.map φ g)⁻¹ : GL n S) : Matrix n n S)) =
        fun g => ((g⁻¹ : GL n R) : Matrix n n R).map φ := by
      funext g; rw [← map_inv]; rfl
    rw [this]
    exact Units.continuous_coe_inv.matrix_map hφ

end Map

theorem deltaHalf_blockMap {K₁ K₂ : Type} [Field K₁] [ValuativeRel K₁] [TopologicalSpace K₁]
    [IsNonarchimedeanLocalField K₁] [Field K₂] [ValuativeRel K₂] [TopologicalSpace K₂]
    [IsNonarchimedeanLocalField K₂] (φ : K₂ →+* K₁)
    (hn : ∀ y : K₂ˣ, nabs K₁ (Units.map φ.toMonoidHom y) = nabs K₂ y) (L : Levi K₂ m) :
    deltaHalf K₁ m (blockMap φ L) = deltaHalf K₂ m L := by
  rw [deltaHalf_apply, deltaHalf_apply]
  refine Finset.prod_congr rfl fun a _ => Units.ext ?_
  rw [val_absPow, val_absPow, blockMap_apply, GeneralLinearGroup.map_det]
  exact congrArg (fun r : ℝ => ((r : ℂ)) ^ _) (hn _)

theorem multiProd_comp_glMap : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k'), Continuous i → Continuous i.symm → (∀ x : kˣ, GlobalTheory.SplitWeil.nabs k' (Units.map i.toRingHom.toMonoidHom x) = GlobalTheory.SplitWeil.nabs k x) → ∀ {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)), Nonempty (Representation.Equiv ((GlobalTheory.SmGL.multiProd e σ).comp (Matrix.GeneralLinearGroup.map (n := n) i.symm.toRingHom)) (GlobalTheory.SmGL.multiProd e fun a => (σ a).comp (Matrix.GeneralLinearGroup.map (n := m a) i.symm.toRingHom))) := by
  intro k k' _ _ _ _ _ _ _ _ i hi hi' hn α n m _ _ _ _ _ _ e X _ _ σ
  have hn' : ∀ y : k'ˣ, nabs k (Units.map i.symm.toRingHom.toMonoidHom y) = nabs k' y := fun y => by
    have h := hn (Units.map i.symm.toRingHom.toMonoidHom y)
    rw [show Units.map i.toRingHom.toMonoidHom (Units.map i.symm.toRingHom.toMonoidHom y) = y from
      Units.ext (by simp)] at h
    exact h.symm
  let Φ := pullMap e (ρ₁ := piTensor σ) (ρ₂ := piTensor fun a => (σ a).comp
      (GeneralLinearGroup.map (n := m a) i.symm.toRingHom))
    (GeneralLinearGroup.map i.symm.toRingHom) (continuous_glMap _ hi')
    (blockMap i.symm.toRingHom) (fun p => map_mem_parab e _ p) (fun p => leviProj_map e _ p)
    (fun _ => rfl) (fun L => deltaHalf_blockMap _ hn' L)
  let Ψ := pullFun e (ρ₁ := piTensor fun a => (σ a).comp
      (GeneralLinearGroup.map (n := m a) i.symm.toRingHom)) (ρ₂ := piTensor σ)
    (GeneralLinearGroup.map i.toRingHom) (continuous_glMap _ hi)
    (blockMap i.toRingHom) (fun p => map_mem_parab e _ p) (fun p => leviProj_map e _ p)
    (fun L => by
      show piTensor σ L = piTensor σ (fun a => GeneralLinearGroup.map i.symm.toRingHom
        (GeneralLinearGroup.map i.toRingHom (L a)))
      congr 1
      funext a
      ext
      simp) (fun L => deltaHalf_blockMap _ hn L)
  refine ⟨GlobalTheory.LocGL.equivOfBijective Φ (Function.bijective_iff_has_inverse.2 ⟨Ψ, fun f => ?_, fun f => ?_⟩)⟩
  · refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    show f.1.1 (GeneralLinearGroup.map i.symm.toRingHom (GeneralLinearGroup.map i.toRingHom x)) = f.1.1 x
    rw [show GeneralLinearGroup.map i.symm.toRingHom (GeneralLinearGroup.map i.toRingHom x) = x from
      Matrix.GeneralLinearGroup.ext fun _ _ => by simp]
  · refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    show f.1.1 (GeneralLinearGroup.map i.toRingHom (GeneralLinearGroup.map i.symm.toRingHom x)) = f.1.1 x
    rw [show GeneralLinearGroup.map i.toRingHom (GeneralLinearGroup.map i.symm.toRingHom x) = x from
      Matrix.GeneralLinearGroup.ext fun _ _ => by simp]

end GlobalTheory.IndField
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

noncomputable section

namespace GlobalTheory.SchurExt.InvParts

theorem L_bridge : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (x : GA E (m + r + 1 + 1)) (k : GL (Fin (m + r + 1 + 1)) (Af E)), IsUnit (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det → IsUnit (Dof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))).det → IsUnit (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det ∧ IsUnit (Dof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det ∧ mkGL (Dof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) = mkGL (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) * finGL E (r + 1) (mkGL (Dof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))))) ∧ mkGL (Scof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) = mkGL (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) * finGL E (m + 1) (mkGL (Scof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))))) ∧ (∀ i j, pInf E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) = pInf E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j)) ∧ (∀ i j, pFin E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) = pFin E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) + Yof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) i j) ∧ Xof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) 0 = Xof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) 0 + sFin E (∑ j, ∑ l, pFin E (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) j) * Xof (conjLowUni ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) j l * pFin E ((Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))⁻¹ l 0)) := GlobalTheory.T.isUnit_block_det_of_conj_lower

theorem L_top : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (Uβ : Subgroup (GL (Fin (m + 1)) (Af E))) (Ub : Subgroup (GL (Fin (r + 1)) (Af E))), IsOpen (Uβ : Set (GL (Fin (m + 1)) (Af E))) → IsOpen (Ub : Set (GL (Fin (r + 1)) (Af E))) → ∀ (Krow : Set (Fin (m + 1) → Af E)) (Kcol : Set (Fin (r + 1) → Af E)), IsCompact Krow → IsCompact Kcol → ∃ W ∈ 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)), ∀ k ∈ W, (∀ w ∉ S, Matrix.GeneralLinearGroup.map (pLoc E w) k = 1) → ∀ Y : Matrix (Fin (r + 1)) (Fin (m + 1)) (Af E), (∀ i j, Y i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) → IsUnit (Dof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))).det ∧ mkGL (Dof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))) ∈ Ub ∧ mkGL (Scof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E)))) ∈ Uβ ∧ (∀ i j, Yof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) ∧ ∀ ρ ∈ Krow, ∀ γ ∈ Kcol, (∑ j, ∑ l, ρ j * Xof (conjLowUni Y (k : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Af E))) j l * γ l) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := GlobalTheory.T.exists_nhds_one_conjLowerUnipotent_schurBlocks_small

theorem L_row : ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ), (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) → ∃ K : Set (Fin (m + 1) → Af E), IsCompact K ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → (fun j => pFin E ((h : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j)) ∈ K := GlobalTheory.T.lastRow_finite_mem_compact_on_support

theorem L_col : ∀ (E : Type) [Field E] [NumberField E] (r : ℕ) (b₁ : GA E (r + 1) → ℂ), (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), u⁻¹ * p ∈ C) → ∃ K : Set (Fin (r + 1) → Af E), IsCompact K ∧ ∀ p, b₁ p ≠ 0 → (fun l => pFin E (((p⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)) l 0)) ∈ K := GlobalTheory.T.firstColumn_inv_finite_mem_compact_on_support

theorem L_supSc : ∀ (E : Type) [Field E] [NumberField E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (x : GA E (m + r + 1 + 1)), x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S → IsUnit (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det → mkGL (Scof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S := GlobalTheory.T.schurComplement_mem_adelicGLSupportedAtFinitePlaces

end GlobalTheory.SchurExt.InvParts

namespace GlobalTheory.SchurExt

variable {E : Type} [Field E] [NumberField E]

theorem psi_sFin_of_mem {z : Af E} (hz : z ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) : psi (sFin E z) = 1 := by
  have h := GroundTheory.Global.adelicChar_of_mem_invDifferentAdeles (K := E) (y := sFin E z)
    (GroundTheory.Global.mem_invDifferentAdeles.mpr (GroundTheory.Global.mem_finiteInvDifferent_of_mem_integralFiniteAdeles hz))
  have h0 : (sFin E z).1 = 0 := rfl
  rw [psi, h, h0]
  simp

theorem psi_add (a b : Ad E) : psi (a + b) = psi a * psi b := by
  simp only [psi, AddChar.map_add_eq_mul, Circle.coe_mul]

theorem supS_mul {a : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))} {x y : GA E a}
    (hx : x ∈ GlobalTheory.JSW.supS (E := E) (a := a) S) (hy : y ∈ GlobalTheory.JSW.supS (E := E) (a := a) S) : x * y ∈ GlobalTheory.JSW.supS (E := E) (a := a) S := by
  intro w hw
  rw [map_mul, hx w hw, hy w hw, mul_one]

theorem supS_inv {a : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))} {x : GA E a}
    (hx : x ∈ GlobalTheory.JSW.supS (E := E) (a := a) S) : x⁻¹ ∈ GlobalTheory.JSW.supS (E := E) (a := a) S := by
  intro w hw
  rw [map_inv, hx w hw, inv_one]

theorem finGL_mem_supS {a : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))} {k : GL (Fin a) (Af E)}
    (hk : finGL E a k ∈ GlobalTheory.JSW.supS (E := E) (a := a) S) (w : HeightOneSpectrum (𝓞 E)) (hw : w ∉ S) :
    Matrix.GeneralLinearGroup.map (pLoc E w) k = 1 := by
  have h := hk w hw
  rw [← h]
  refine Units.ext (Matrix.ext fun i j => ?_)
  change pLoc E w (k i j) = pLoc E w (pFin E ((finGL E a k : GA E a) i j))
  congr 1
  exact (congrArg (fun y : GL (Fin a) (Af E) => (y : Matrix (Fin a) (Fin a) (Af E)) i j) (pFin_finGL (E := E) k)).symm

end GlobalTheory.SchurExt


open GlobalTheory.SchurExt.InvParts in
theorem GlobalTheory.SchurExt.schurF_mul_finGL_eq : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ), (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, β (g * finGL E (m + 1) u) = β g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, β h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * h ∈ C) → (∃ U : Subgroup (GL (Fin (r + 1)) (Af E)), IsOpen (U : Set (GL (Fin (r + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b₁ (g * finGL E (r + 1) u) = b₁ g) → (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (r + 1)), u⁻¹ * p ∈ C) → ∃ W ∈ 𝓝 (1 : GL (Fin (m + r + 1 + 1)) (Af E)), ∀ k ∈ W, finGL E (m + r + 1 + 1) k ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S → ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S, schurF β b₁ χ (x * finGL E (m + r + 1 + 1) k) = schurF β b₁ χ x := by
  intro E _ _ _ m r S β b₁ χ ⟨Uβ, hUβo, hUβ⟩ hβC ⟨Ub, hUbo, hUb⟩ hbC
  obtain ⟨Krow, hKr, hKrow⟩ := L_row E m S β hβC
  obtain ⟨Kcol, hKc, hKcol⟩ := L_col E r b₁ hbC
  obtain ⟨W₀, hW₀, hW⟩ := L_top E m r S Uβ Ub hUβo hUbo Krow Kcol hKr hKc
  have fwd : ∀ k ∈ W₀, finGL E (m + r + 1 + 1) k ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S →
      ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + r + 1 + 1)) S, schurF β b₁ χ x ≠ 0 →
        schurF β b₁ χ (x * finGL E (m + r + 1 + 1) k) = schurF β b₁ χ x := by
    intro k hk hkS x hx hF
    classical
    have hD : IsUnit (Dof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det := by
      by_contra hD
      exact hF (by rw [schurF, ite_eq_right hD])
    rw [schurF, ite_eq_left hD] at hF
    have hβ0 := left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hF))
    have hβ0' := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hF))
    have hb0 := right_ne_zero_of_mul (left_ne_zero_of_mul hF)
    have hχ0 := right_ne_zero_of_mul hF
    have hYint : ∀ i j, pFin E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) ∈
        GroundTheory.Global.integralFiniteAdeles (𝓞 E) E := by
      by_contra hY
      exact hχ0 (by rw [chiF, ite_eq_right hY, mul_zero])
    obtain ⟨hdu, hdU, hsU, hyI, hX⟩ := hW k hk (finGL_mem_supS hkS)
      ((Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).map (pFin E)) (fun i j => hYint i j)
    obtain ⟨hSc, hD', eD, eSc, eYi, eYf, eX⟩ := L_bridge E m r x k hD hdu
    have hrow := hKrow _ (L_supSc E m r S x hx hD) hβ0'
    have hcol := hKcol _ hb0
    rw [coe_mkGL hSc] at hrow
    rw [Matrix.coe_units_inv, coe_mkGL hD] at hcol
    have hz := hX _ hrow _ hcol
    have hchi : chiF χ (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) :
        Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) =
        chiF χ (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))) := by
      have h1 : (fun i j => pInf E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) :
          Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j)) =
          fun i j => pInf E (Yof (x : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) :=
        funext fun i => funext fun j => eYi i j
      have h2 : ∀ i j, pFin E (Yof ((x * finGL E (m + r + 1 + 1) k : GA E (m + r + 1 + 1)) :
          Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) i j) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E :=
        fun i j => by rw [eYf]; exact add_mem (hYint i j) (hyI i j)
      rw [chiF, chiF, h1, ite_eq_left h2, ite_eq_left hYint]
    rw [schurF, ite_eq_left hD', eD, eSc, hUb _ hdU, hUβ _ hsU, hchi, eX, psi_add, psi_sFin_of_mem hz, mul_one, schurF, ite_eq_left hD]
  open scoped Pointwise in
  exact by
    refine ⟨W₀ ∩ W₀⁻¹, Filter.inter_mem hW₀ (inv_mem_nhds_one _ hW₀), ?_⟩
    intro k hk hkS x hx
    by_cases h0 : schurF β b₁ χ x = 0
    · by_cases h1 : schurF β b₁ χ (x * finGL E (m + r + 1 + 1) k) = 0
      · rw [h0, h1]
      · have h2 := fwd k⁻¹ hk.2 (by rw [map_inv]; exact supS_inv hkS) _ (supS_mul hx hkS) h1
        rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one] at h2
        exact absurd (h2.symm.trans h0) h1
    · exact fwd k hk.1 hkS x hx h0
end
end

section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.SenLines GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen GlobalTheory.CycFr GlobalTheory.WachTie

namespace GlobalTheory.SenLines

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {l : ℕ}

theorem isUnit_q_of_associated {m : ℕ} (h : Associated W.π₀₁ (X ^ m)) :
    IsUnit (algebraMap (LetA O n) W.EE (W.π₀ + ((PD.p : ℕ) : LetA O n))) := by
  obtain ⟨w, hw⟩ := h.symm
  have e : (W.π₀ : LetA O n) = letπ ^ m * fun _ => (w : O⟦X⟧) := funext fun _ => hw.symm
  have hu : IsUnit (algebraMap (LetA O n) W.EE W.π₀) := by
    rw [e, map_mul, map_pow]
    exact (W.EE_π.pow _).mul (IsUnit.map _ (Pi.isUnit_iff.2 fun _ => w.isUnit))
  haveI := W.EE_complete
  have hJ := IsAdicComplete.le_jacobson_bot (Ideal.span {((PD.p : ℕ) : W.EE)})
    (Ideal.mem_span_singleton_self _)
  obtain ⟨u, hu⟩ := hu
  have h1 := (Ideal.mem_jacobson_bot.1 hJ (↑u⁻¹ : W.EE)).mul u.isUnit
  rw [map_add (f := _), map_natCast, ← hu]
  convert h1 using 1
  rw [add_mul, mul_assoc, Units.inv_mul]; ring

variable [Fact l.Prime] [IsDomain O] [CharZero O] [Algebra ℤ_[l] O] (hp : PD.p = l)
  (χ : W.Gam →* ℤ_[l]ˣ) (hχ : ∀ g, algebraMap ℤ_[l] O (χ g : ℤ_[l]) = (W.χΓ g : O))
include hp hχ

theorem exists_subst_invariants (ξ : O⟦X⟧) (hξ : Associated ξ (X ^ W.DelF.card))
    (h0 : constantCoeff ξ = 0) (hinv : ∀ δ ∈ W.DelF, W.γ₀ δ ξ = ξ) :
    ∃ j : O⟦X⟧ →ₐ[O] O⟦X⟧, j X = ξ ∧ Function.Injective j ∧
      ∀ a, (∃ b, j b = a) ↔ ∀ δ ∈ W.DelF, W.γ₀ δ a = a := by
  classical
  have hγ := γ₀_eq W hp χ hχ
  have hχi : Function.Injective χ := fun a b hab =>
    W.χΓ_inj (Units.ext (by rw [← hχ, ← hχ, hab]))
  let Δ : Subgroup ℤ_[l]ˣ := (CommGroup.torsion W.Gam).map χ
  have hΔ : (Δ : Set ℤ_[l]ˣ) = ↑(W.DelF.image χ) := by
    ext x
    simp only [Δ, Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, CommGroup.mem_torsion,
      Finset.coe_image, Finset.mem_coe, mem_DelF_iff]
  have hfa : ∀ p : ℤ_[l]ˣ → Prop, (∀ δ ∈ Δ, p δ) ↔ ∀ δ ∈ W.DelF, p (χ δ) := by
    intro p
    simp only [← SetLike.mem_coe, hΔ, Finset.coe_image, Set.forall_mem_image]
  haveI : Finite Δ := by
    change Finite (Δ : Set ℤ_[l]ˣ)
    rw [hΔ]; infer_instance
  have hcard : Nat.card Δ = W.DelF.card := by
    change Nat.card (Δ : Set ℤ_[l]ˣ) = _
    rw [hΔ, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_image_of_injective _ hχi]
  have hs : HasSubst ξ := HasSubst.of_constantCoeff_zero' h0
  have hX : (substAlgHom hs : O⟦X⟧ →ₐ[O] O⟦X⟧) X = ξ := by rw [coe_substAlgHom, subst_X hs]
  obtain ⟨h2, h3⟩ := injective_and_range_eq_invariants Δ (substAlgHom hs : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (by rw [hX, hcard]; exact hξ)
    ((hfa _).2 fun δ hδ => by rw [← hγ, hX]; exact hinv δ hδ)
  refine ⟨_, hX, h2, fun a => ?_⟩
  rw [h3, hfa]; simp only [hγ]

theorem exists_qFrame_of_card [IsNoetherianRing O] (hl : l ≠ 2) (hc : W.DelF.card = l - 1)
    (σ : O⟦X⟧ ≃ₐ[O] O⟦X⟧) (hσ : σ X = X + C (l : O)) (g : W.Gam)
    (hg : (l : ℤ_[l]) ∣ (χ g : ℤ_[l]) - 1) : ∃ J, QFrame W g J := by
  have h2l := (Fact.out : l.Prime).two_le
  have hl0 : (l : O) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨p2, p3, w, hw⟩ := π₀₁_spec W hp χ hχ hl hc
  have hq := (φ₀_eq W hp).2
  have hγ := γ₀_eq W hp χ hχ
  have hX0 : (X : O⟦X⟧) ∣ W.π₀₁ := (dvd_pow_self _ (by omega)).trans p2.symm.dvd
  have h0 := X_dvd_iff.1 hX0
  obtain ⟨j, hj, hji, hjr⟩ := exists_subst_invariants W hp χ hχ _ p2 h0 p3
  let J : O⟦X⟧ →ₐ[O] O⟦X⟧ := j.comp σ
  have hJ : ∀ c, J c = j (σ c) := fun _ => rfl
  have hσ' : σ X = X + (l : O⟦X⟧) := by rw [hσ, map_natCast]
  have hJX : J X = W.π₀₁ + (l : O⟦X⟧) := by rw [hJ, hσ', map_add (f := _), hj, map_natCast]
  have hσl : σ (X - (l : O⟦X⟧)) = X := by rw [map_sub, hσ', map_natCast]; ring
  have hr : ∀ a, (∃ b, J b = a) ↔ ∀ δ ∈ W.DelF, W.γ₀ δ a = a := fun a => by
    rw [← hjr]
    exact ⟨fun ⟨b, hb⟩ => ⟨σ b, hb⟩, fun ⟨b, hb⟩ => ⟨σ.symm b, by rw [hJ, σ.apply_symm_apply, hb]⟩⟩
  have hk : ∀ c, constantCoeff (J c) = 0 → X - (l : O⟦X⟧) ∣ c := fun c h => by
    rw [hJ, constantCoeff_algHom j (hj ▸ hX0)] at h
    rw [← map_dvd_iff σ, hσl, X_dvd_iff, h]
  have hc0 : constantCoeff (J X) = (l : O) := by rw [hJX, map_add (f := _), h0, map_natCast, zero_add]
  have hwu : IsUnit w := by
    have h1 := congrArg constantCoeff hw
    rw [← hJX, hc0, map_mul, show constantCoeff (lvl l O 0) = (l : O) by simp [lvl]] at h1
    rw [isUnit_iff_constantCoeff, ← mul_left_cancel₀ hl0 ((mul_one _).trans h1)]
    exact isUnit_one
  have hass : Associated (J X) (lvl l O 0) := by
    rw [hJX, hw]; exact associated_mul_unit_left _ _ hwu
  have hne : J X ≠ 0 := fun h => hl0 (by rw [← hc0, h, map_zero])
  obtain ⟨y, hy⟩ : J X * X ∣ W.γ₀ g (J X) - J X := by
    have h1 := dvd_act_sub (O := O) 1 (χ g) 1 (by rwa [pow_one]) (J X)
    have h2 := mul_lvl (l := l) (O := O) 0
    rw [pow_zero, pow_one, add_sub_cancel_left, zero_add] at h2
    rw [act_one, ← hγ, ← h2, mul_comm] at h1
    exact (mul_dvd_mul_right hass.dvd _).trans h1
  have hinv := (hr (J X)).1 ⟨X, rfl⟩
  obtain ⟨y', hy'⟩ := (hr (X * y)).2 fun δ hδ => by
    apply mul_left_cancel₀ hne
    have h1 := congrArg (W.γ₀ δ) hy
    rw [mul_assoc, map_mul, map_sub, hinv δ hδ, hγ δ, hγ g, act_comm, ← hγ δ, hinv δ hδ,
      ← hγ g, hy, mul_assoc] at h1
    exact h1.symm
  obtain ⟨z, hz⟩ := hk y' (by rw [hy']; simp)
  have hs : IsUnit (1 + y') := by
    rw [← MulEquiv.isUnit_map σ, hz, map_add (f := _), map_mul, hσl, isUnit_iff_constantCoeff]
    simp
  refine ⟨J, hji.comp σ.injective, hr, by rw [hp, hJX], by rw [hp]; exact hk,
    ⟨hs.unit, ?_, ?_⟩, hq ▸ hass, isUnit_q_of_associated W p2⟩
  · rw [hs.unit_spec, map_add (f := _), map_one, hy']
    linear_combination hy
  · rw [hp, hs.unit_spec, add_sub_cancel_left]
    exact ⟨z, hz⟩

end Generic

theorem exists_qFrame : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ} (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (g : W.Gam), CaseA K LL → ((W.χΓ g : (↥(OL LL))ˣ) : ↥(OL LL)) = 1 + (l : ↥(OL LL)) → IsUnit (W.DelF.card : ↥(OL LL)) ∧ ∃ J, QFrame W g J := by
  intro l _ P K LL n W g ⟨hK, hl, h⟩ hg
  have p1 : Module.finrank ↥(K0 K) ↥K.1 = 1 := by
    rw [Algebra.finrank_eq_one_iff_bijective_algebraMap]
    exact ⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun x => ⟨⟨x.1, x.2, hK x.2⟩, rfl⟩⟩
  have hc := GlobalTheory.TorsionCard.card_torsion_mul_finrank P K LL W hl h.2.2.1
  rw [p1, mul_one] at hc
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.exists_cyclotomicChar_padicInt_units P K LL W
  obtain ⟨_, _, hu⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  obtain ⟨σ, hσ⟩ := GlobalTheory.NB.LT.exists_algEquiv_X_add_C (IsLocalRing.maximalIdeal ↥(OL LL))
    (l : ↥(OL LL)) hu
  refine ⟨?_, exists_qFrame_of_card W (P.PD_p K) χ hχ hl hc σ hσ g ?_⟩
  · have h1 := IsLocalRing.isUnit_or_isUnit_one_sub_self (l : ↥(OL LL))
    rw [hc, Nat.cast_sub (Fact.out : l.Prime).one_le, Nat.cast_one, ← IsUnit.neg_iff, neg_sub]
    exact h1.resolve_left hu
  · have h1 : (χ g : ℤ_[l]) = 1 + l := GlobalTheory.algebraMap_padicInt_OL_injective LL (by
      rw [hχ, hg, map_add (f := _), map_one, map_natCast])
    rw [h1, add_sub_cancel_left]

end GlobalTheory.SenLines
end

section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual



theorem _root_.GlobalTheory.T.crystalline_potential_family : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → PotDRL D.loc → admBK (D := D) → ∀ (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 → ∀ n : ℕ,
      PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
    ∀ (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hSub : SubTw i r Xs M),
      IsDR (Br.PD D.loc D.nbr i w hw) (locU i w hw M hSub.1).ρ ∧
      ∃ (U' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
        (PU : (locU i w hw M hSub.1).V →ₗ[Br.LL D.nbr i w hw] U'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw),
        IsSubFam (fun x : ↥Xs => Br.loc D.nbr i w hw (rDuO D.nd i r x)) U' ∧
        DualLatLe (Br.PD D.loc D.nbr i w hw) (locU i w hw M hSub.1) U' (Br.locLat D.nbr i w hw M) PU (2 * k) := by
  first | exact @GlobalTheory.Pass.LocDualU.main | exact GlobalTheory.Pass.LocDualU.main | (intros; apply GlobalTheory.Pass.LocDualU.main <;> assumption)
end
