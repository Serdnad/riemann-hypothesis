module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle114
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import GroundTheory.AutomorphicForms.InductionParabolic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle221
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle209
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle210
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle211
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle212
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RefinedBlockOrderCompat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle181
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.ConstantTerm
import GroundTheory.AutomorphicForms.Bundle012
import GroundTheory.GlobalFields.Adele.Topology
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.HasModerateGrowthZero
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStructure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle205
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle223
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle216
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle224
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle225
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle214
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.AutLevel

variable (E : Type) [Field E] [NumberField E] (a : ℕ)

theorem finEmb_eq_finGL (k : AdelicGLn.FiniteAdelicGL E a) :
    AutomorphicForm.finEmb E a k = finGL E a k := by
  apply (AdelicGLn.prodEquiv E a).injective
  rw [AutomorphicForm.prodEquiv_finEmb]
  have s1 : ∀ x, (sFin E x).1 = 0 := fun _ => rfl
  have s2 : ∀ x, (sFin E x).2 = x := fun _ => rfl
  refine Prod.ext (Units.ext (Matrix.ext fun i j => ?_)) (Units.ext (Matrix.ext fun i j => ?_))
  · change (1 : Matrix (Fin a) (Fin a) (InfiniteAdeleRing E)) i j =
      ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j).1 -
        (sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)).1 + (sFin E (k i j)).1
    rw [s1, s1, sub_zero, add_zero]
    by_cases h : i = j
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
      rfl
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h]
      rfl
  · change k.1 i j =
      ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j).2 -
        (sFin E ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)).2 + (sFin E (k i j)).2
    rw [s2, s2]
    have h1 : ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j).2 = (1 : Matrix (Fin a) (Fin a) (Af E)) i j := by
      by_cases h : i = j
      · subst h
        rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
        rfl
      · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h]
        rfl
    rw [h1, sub_self, zero_add]

theorem exists_open_level : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → (∃ U : Subgroup (AdelicGLn.integralFiniteGL E a), IsOpen (U : Set (AdelicGLn.integralFiniteGL E a)) ∧
    ∀ (g : AdelicGLn.AdelicGL E a) (u : U), φ.1 (g * AutomorphicForm.finEmb E a ((u : AdelicGLn.integralFiniteGL E a) : AdelicGLn.FiniteAdelicGL E a)) = φ.1 g) := by
  intro E _ _ _ a φ hφ
  let S : Subgroup (AdelicGLn.FiniteAdelicGL E a) :=
    { carrier := {k | finRep E a k φ = φ}
      mul_mem' := fun {x y} hx hy => by
        change finRep E a (x * y) φ = φ
        rw [map_mul, Module.End.mul_apply, hy, hx]
      one_mem' := by
        change finRep E a 1 φ = φ
        rw [map_one, Module.End.one_apply]
      inv_mem' := fun {x} hx => by
        change finRep E a x⁻¹ φ = φ
        have h : finRep E a x⁻¹ (finRep E a x φ) = φ := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rwa [hx] at h }
  refine ⟨S.subgroupOf (AdelicGLn.integralFiniteGL E a), ?_, ?_⟩
  · exact hφ.level.preimage continuous_subtype_val
  · intro g u
    have hu : finRep E a ((u : AdelicGLn.integralFiniteGL E a) : AdelicGLn.FiniteAdelicGL E a) φ = φ :=
      Subgroup.mem_subgroupOf.1 u.2
    rw [finEmb_eq_finGL]
    exact congrArg (fun ψ : Sm E a => ψ.1 g) hu

end GlobalTheory.CompanionTheory.AutLevel
end

section

noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.CuspBridge

theorem unipGL_eq_unip {R : Type} [CommRing R] {a r : ℕ} (X : AutomorphicForm.UPos a r → R) :
    AutomorphicForm.unipGL X = unip X := by
  apply Units.ext
  rfl

theorem isAddHaarMeasure_unipMeasure (E : Type) [Field E] [NumberField E] (a r : ℕ) :
    (AutomorphicForm.unipMeasure E a r).IsAddHaarMeasure := by
  infer_instance

theorem isCuspidal_of_isCuspForm : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    IsCuspForm φ → AutomorphicForm.IsCuspidal φ.1 := by
  intro E _ _ _ a φ h r h0 h1 g
  have h2 := h.2 r h0 h1 (AutomorphicForm.unipMeasure E a r) (AutomorphicForm.unipFundamentalDomain E a r)
    (isAddHaarMeasure_unipMeasure E a r) AutomorphicForm.isAddFundamentalDomain_unipFundamentalDomain g
  simpa only [AutomorphicForm.constantTerm, unipGL_eq_unip] using h2

end GlobalTheory.CompanionTheory.CuspBridge

end
end

section

open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.LeftInv

theorem ratGL_eq_diagonal (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (γ : GL (Fin a) E) : ratGL E a γ = AdelicGLn.diagonal E a γ :=
  Units.ext (Matrix.ext fun _ _ => rfl)

theorem isLeftInvariant_of_isAutForm : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (a : ℕ) (φ : Sm E a), IsAutForm φ → AutomorphicForm.IsLeftInvariant φ.1 := by
  intro E _ _ _ a φ h γ g
  rw [← ratGL_eq_diagonal]
  exact h.left γ g

end GlobalTheory.CompanionTheory.LeftInv
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical


theorem _root_.GlobalTheory.T.local_galois_embedding_extension : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw → ∀ (LL' : FinExt l), Bw.LL.1 ≤ LL'.1 →
    ∀ (j : {j : w.adicCompletion E →+* Qbar l // Continuous j}),
    ∃ (φ : w.adicCompletion E →+* Om l) (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), Continuous φ ∧
      (∀ y : E, φ (algebraMap E (w.adicCompletion E) y) = Bw.j (algebraMap E Ω y)) ∧
      (∀ x, ∃ hx : φ x ∈ Bw.Kw.1, ((τ ⟨φ x, hx⟩ : ↥LL'.1) : Om l) = j.1 x) ∧
      ∀ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1,
        IsInduced Bw (j.1.comp (algebraMap E (w.adicCompletion E))) τ' ↔ τ' = τ := by
  first | exact @GlobalTheory.CompanionTheory.EmbBridge.embeddings_of_continuous | exact GlobalTheory.CompanionTheory.EmbBridge.embeddings_of_continuous | (intros; apply GlobalTheory.CompanionTheory.EmbBridge.embeddings_of_continuous <;> assumption)
end
end

section

open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.CycWordTrace

theorem sum_cycWord_eq_etr : ∀ (B : Type) [Ring B] (n m : ℕ) (X : Fin n → Fin n → B),
    ∑ a : Fin (m + 1) → Fin n, ((GlobalTheory.Dec.cycWord a).map fun p => X p.1 p.2).prod
      = Formalism.REAL.etr X (m + 1) := by
  intro B _ n m X
  exact (GlobalTheory.TraceCycWord.etr_succ_eq_sum_cycWord X m).symm

end GlobalTheory.CompanionTheory.CycWordTrace
end

section

theorem GlobalTheory.CompanionTheory.ModelS.gelfVal_perm :
    ∀ (n : ℕ) (χ : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) (k : ℕ),
      GlobalTheory.Dec.gelfVal (fun a => χ (σ a)) k = GlobalTheory.Dec.gelfVal χ k :=
  fun _ χ σ k => GlobalTheory.CompanionTheory.WaveMult.gelfVal_comp_perm χ σ k
end

section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.ParIndBridge

theorem parInd_equiv_parabolicInd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (φ : Levi k m ≃* levi k N β), (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) → ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W), Nonempty ((parInd e ρ).Equiv (parabolicInd k N β (ρ.comp φ.symm.toMonoidHom))) := by
  intro k _ _ _ _ α _ _ N m _ _ e β hβ φ hφ W _ _ ρ
  have hP : parab k e = blockUpper k N β := GlobalTheory.T.parabolic_eq_block_upper k e β hβ
  have h12 : ∀ {p : GL (Fin N) k}, p ∈ parab k e → p ∈ blockUpper k N β := fun h => hP ▸ h
  have h21 : ∀ {p : GL (Fin N) k}, p ∈ blockUpper k N β → p ∈ parab k e := fun h => hP ▸ h
  have hchar : ∀ (p : GL (Fin N) k) (h1 : p ∈ parab k e) (h2 : p ∈ blockUpper k N β) (w : W),
      (deltaHalf k m (leviProj k e ⟨p, h1⟩) : ℂ) • ρ (leviProj k e ⟨p, h1⟩) w =
        sqrtModular k N β ⟨p, h2⟩ •
          ρ (φ.symm (GroundTheory.Automorphic.Parabolic.leviProj k N β ⟨p, h2⟩)) w := by
    intro p h1 h2 w
    have hL := GlobalTheory.T.parabolic_levi_projection k e β hβ φ hφ p h1 h2
    rw [← hL, MulEquiv.symm_apply_apply, GlobalTheory.T.modulus_character_levi k e β hβ φ hφ, hL,
      GroundTheory.Automorphic.Parabolic.sqrtModular_leviProj]
  let σ := ρ.comp φ.symm.toMonoidHom
  let E : IndSp e ρ ≃ₗ[ℂ] GroundTheory.Automorphic.Parabolic.parabolicIndSpace k N β σ :=
    { toFun := fun f => ⟨f.1.1, fun p g => by
          have h := parInd_law e ρ f ⟨p.1, h21 p.2⟩ g
          refine h.trans ?_
          exact hchar p.1 (h21 p.2) p.2 _,
        GroundTheory.Automorphic.stabilizerOf (GlobalTheory.PRep.ind (parab k e)
          ((twist ρ (deltaHalf k m)).comp (leviProj k e))) f.1, f.2, fun x hx g => by
          have h := GroundTheory.Automorphic.mem_stabilizerOf.1 hx
          exact congrFun (congrArg Subtype.val h) g⟩
      invFun := fun f => ⟨⟨f.1, fun p g => by
          have h := f.2.1 ⟨p.1, h12 p.2⟩ g
          refine h.trans ?_
          exact (hchar p.1 p.2 (h12 p.2) _).symm⟩, by
          obtain ⟨-, K, hK, hf⟩ := f.2
          refine mem_smoothPart_of_nhds (Filter.mem_of_superset (hK.mem_nhds (one_mem K)) fun x hx => ?_)
          exact Subtype.ext (funext fun g => hf x hx g)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact ⟨Representation.Equiv.mk E fun g => LinearMap.ext fun f => Subtype.ext (funext fun x => rfl)⟩

end GlobalTheory.CompanionTheory.ParIndBridge
end

section

set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.HCRep

open AutomorphicForm GlobalTheory.CompanionTheory.ArchSmooth

theorem exists_skew_curve {E : Type} [Field E] [NumberField E] {a : ℕ} (S : Matrix (Fin a) (Fin a) (Cinf E)) :
    ∃ c : ℝ → GL (Fin a) (Cinf E), c 0 = 1 ∧ HasDerivAt (fun t => toL (c t).val) (toL S) 0 ∧
      (S.conjTranspose = -S → ∀ t, (c t).val ∈ Matrix.unitaryGroup (Fin a) (Cinf E)) := by
  refine ⟨fun t => (Matrix.isUnit_exp (t • S)).unit, Units.ext (by simp), ?_, fun hS t => ?_⟩
  · open scoped Matrix.Norms.Operator in
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) S (0 : ℝ)
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
    exact h
  · rw [IsUnit.unit_spec, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose,
      Matrix.conjTranspose_smul, hS, star_trivial, smul_neg,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • S)).neg_left, neg_add_cancel, NormedSpace.exp_zero]

theorem liB_skew_mem_span : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a)
    (Z : (AutomorphicForm.isExpLieAlgebra E a).lieSubalgebra),
    Matrix.conjTranspose (AutomorphicForm.mat (Z : AutomorphicForm.ArchMatrix E a)) =
      -AutomorphicForm.mat (Z : AutomorphicForm.ArchMatrix E a) →
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) →
    ∀ ψ ∈ Submodule.span ℂ (Set.range fun k => cptRep E a k φ),
      GlobalTheory.CompanionTheory.HCRep.liB Z ψ ∈ Submodule.span ℂ (Set.range fun k => cptRep E a k φ) := by
  intro E _ _ _ a φ Z hZ hfd ψ hψ
  set W := Submodule.span ℂ (Set.range fun k => cptRep E a k φ) with hW
  have hst : ∀ k : Kinf E a, ∀ w ∈ W, cptRep E a k w ∈ W := by
    intro k w hw
    refine Submodule.span_induction (p := fun w _ => cptRep E a k w ∈ W) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨k', rfl⟩
      refine Submodule.subset_span ⟨k * k', ?_⟩
      change cptRep E a (k * k') φ = cptRep E a k (cptRep E a k' φ)
      rw [map_mul, Module.End.mul_apply]
    · rw [map_zero]; exact W.zero_mem
    · intro x y _ _ hx hy; rw [map_add (f := _)]; exact W.add_mem hx hy
    · intro r x _ hx; rw [map_smul]; exact W.smul_mem r hx
  let S : Matrix (Fin a) (Fin a) (Cinf E) := Matrix.of (mMap E a (Z : ArchMatrix E a))
  have hS : S.conjTranspose = -S := by
    ext i j w
    have h := congrFun (congrFun hZ i) j
    have h2 := congrFun (congrArg Prod.snd h) ⟨w, IsTotallyComplex.isComplex w⟩
    exact h2
  obtain ⟨c, h0, hc, hu⟩ := exists_skew_curve S
  let W' : Submodule ℂ (GA E a → ℂ) := W.map (Sm E a).subtype
  have hW' : FiniteDimensional ℂ W' := inferInstance
  have hF : ∀ t, (fun g => ψ.1 (g * infGL E a (c t))) ∈ W' := fun t =>
    ⟨cptRep E a ⟨(c t).val, hu hS t⟩ ψ, hst _ _ hψ, funext fun g => by
      have e : Unitary.toUnits (⟨(c t).val, hu hS t⟩ : Kinf E a) = c t := Units.ext rfl
      change ψ.1 (g * infGL E a (Unitary.toUnits _)) = _
      rw [e]⟩
  have hd : ∀ g : GA E a, HasDerivAt (fun t : ℝ => ψ.1 (g * infGL E a (c t))) ((liB Z ψ).1 g) 0 :=
    fun g => hasDerivAt_curve ψ g c (toL S) h0 hc
  obtain ⟨w, hw, e⟩ := AutomorphicForm.mem_of_hasDerivAt W' hF hd
  rwa [show liB Z ψ = w from Subtype.ext e.symm]

end GlobalTheory.CompanionTheory.HCRep

end
end

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Sm.normSq {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {u : ℝ → Mat n → W} (hu : Sm u) : Sm fun s y => (‖u s y‖ ^ 2 : ℝ) := by
  have h := ContDiffOn.norm_sq ℝ (show ContDiffOn ℝ ∞ (Function.uncurry u) _ from hu)
  exact h.congr fun z _ => rfl

theorem Sm.inner {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {u v : ℝ → Mat n → W} (hu : Sm u) (hv : Sm v) : Sm fun s y => ⟪u s y, v s y⟫_ℝ := by
  have h := ContDiffOn.inner ℝ (show ContDiffOn ℝ ∞ (Function.uncurry u) _ from hu)
    (show ContDiffOn ℝ ∞ (Function.uncurry v) _ from hv)
  exact h.congr fun z _ => rfl

theorem Sm.add {n : ℕ} {f g : ℝ → Mat n → ℝ} (hf : Sm f) (hg : Sm g) :
    Sm fun s y => f s y + g s y := by
  have h := ContDiffOn.add (show ContDiffOn ℝ ∞ (Function.uncurry f) _ from hf)
    (show ContDiffOn ℝ ∞ (Function.uncurry g) _ from hg)
  exact h.congr fun z _ => rfl

theorem Sm.const_mul {n : ℕ} (c : ℝ) {f : ℝ → Mat n → ℝ} (hf : Sm f) :
    Sm fun s y => c * f s y := by
  have h := ContDiffOn.mul (contDiffOn_const (c := c))
    (show ContDiffOn ℝ ∞ (Function.uncurry f) _ from hf)
  exact h.congr fun z _ => rfl

theorem Sm.sum {n : ℕ} {ι : Type} (t : Finset ι) {f : ι → ℝ → Mat n → ℝ}
    (hf : ∀ i ∈ t, Sm (f i)) : Sm fun s y => ∑ i ∈ t, f i s y := by
  have h := ContDiffOn.sum (s := t) (f := fun i => Function.uncurry (f i))
    (fun i hi => show ContDiffOn ℝ ∞ (Function.uncurry (f i)) _ from hf i hi)
  exact h.congr fun z _ => by simp [Function.uncurry]

theorem sm_dens_inner {n : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (u : ℝ → Mat n → W) (hu : Sm u) :
    Sm (dens u) ∧ ∀ (X : Mat n) (v : ℝ → Mat n → W), Sm v →
      Sm fun s y => ⟪Rt X u s y, v s y⟫_ℝ := by
  obtain ⟨hdt, hRt, -⟩ := GlobalTheory.T.smooth_time_right_derivatives_commute u hu
  refine ⟨?_, fun X v hv => (hRt X).inner hv⟩
  exact (hdt.normSq.add (Sm.const_mul _ (Sm.sum _ fun p _ => (hRt (hm p)).normSq))).add hu.normSq

end GlobalTheory.CompanionTheory.WaveSpd
end
end

section

open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise
open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.cone_measure_density_formula : ∀ n : ℕ, (∀ᵐ v ∂(coneMeas n), v ∈ PositivityTheory.RgBcC.cone n) ∧ ∀ f : (Fin n × Fin n → ℝ) → ℂ, ∫ v, f v ∂(coneMeas n) = ∫ v in PositivityTheory.RgBcC.cone n, f v * ((hOf v).det ^ n)⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.ConeHaar.cone_integral | exact GlobalTheory.CompanionTheory.ConeHaar.cone_integral | (intros; apply GlobalTheory.CompanionTheory.ConeHaar.cone_integral <;> assumption)
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.chart_partial_eq_right_word : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V),
    ContDiffOn ℝ ∞ f (GLs n) → ContDiffOn ℝ ∞ (fun t : Idx n → ℝ => f (1 + cm t)) {t | 1 + cm t ∈ GLs n} ∧
      ∀ (L : List (Idx n)) (t : Idx n → ℝ), 1 + cm t ∈ GLs n →
        pd L (fun t : Idx n → ℝ => f (1 + cm t)) t = Dw L f (1 + cm t) := by
  first | exact @GlobalTheory.CompanionTheory.SobGL.Chart.chart_main | exact GlobalTheory.CompanionTheory.SobGL.Chart.chart_main | (intros; apply GlobalTheory.CompanionTheory.SobGL.Chart.chart_main <;> assumption)
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.derivative_as_right_words : ∀ (n : ℕ) (L : List (Idx n)), ∃ (m : ℕ) (c : Fin m → Mat n → ℝ) (w : Fin m → List (Idx n)),
    (∀ i, ContDiffOn ℝ ∞ (c i) (GLs n)) ∧ ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V),
      ContDiffOn ℝ ∞ f (GLs n) → ∀ y ∈ GLs n, Dw L f y = ∑ i, c i y • Rw (w i) f y := by
  first | exact @GlobalTheory.CompanionTheory.SobGL.Expand.Dw_eq_comb | exact GlobalTheory.CompanionTheory.SobGL.Expand.Dw_eq_comb | (intros; apply GlobalTheory.CompanionTheory.SobGL.Expand.Dw_eq_comb <;> assumption)
end
