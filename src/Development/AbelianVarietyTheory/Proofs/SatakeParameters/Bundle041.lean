module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle031
public import Formalism.SatakeDualWeyl.StatementG
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFieldAdicCompletionTensorOfInert
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle036
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle001
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Ramification
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle005
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle004
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct

namespace GlobalTheory.HoweBridge

section General

variable {G V V' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem irr_twist {π : Representation ℂ G V} (h : π.IsIrreducible) (χ : G →* ℂˣ) :
    (twist π χ).IsIrreducible := by
  let E : Subrepresentation (twist π χ) ≃o Subrepresentation π :=
    { toFun := fun U => ⟨U.toSubmodule, fun g v hv => by
        have h1 := U.toSubmodule.smul_mem (((χ g)⁻¹ : ℂˣ) : ℂ) (U.apply_mem_toSubmodule g hv)
        rwa [twist_apply, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul] at h1⟩
      invFun := fun U => ⟨U.toSubmodule, fun g v hv => by
        rw [twist_apply]
        exact U.toSubmodule.smul_mem _ (U.apply_mem_toSubmodule g hv)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  haveI : IsSimpleOrder (Subrepresentation π) := h
  exact E.isSimpleOrder

theorem irr_comp {π : Representation ℂ G V} (φ : G →* G) (hφ : Function.Surjective φ)
    (h : π.IsIrreducible) : Representation.IsIrreducible (π.comp φ : Representation ℂ G V) := by
  let E : Subrepresentation (π.comp φ : Representation ℂ G V) ≃o Subrepresentation π :=
    { toFun := fun U => ⟨U.toSubmodule, fun g v hv => by
        obtain ⟨g, rfl⟩ := hφ g
        exact U.apply_mem_toSubmodule g hv⟩
      invFun := fun U => ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule (φ g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  haveI : IsSimpleOrder (Subrepresentation π) := h
  exact E.isSimpleOrder

theorem equiv_of_twist {σ : Representation ℂ G V} {σ' : Representation ℂ G V'} (χ : G →* ℂˣ)
    (e : (twist σ χ).Equiv (twist σ' χ)) : Nonempty (σ.Equiv σ') := by
  refine ⟨Representation.Equiv.mk e.toLinearEquiv fun g => LinearMap.ext fun v => ?_⟩
  have h1 := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v
  simp only [LinearMap.comp_apply]
  change e.toIntertwiningMap (σ g v) = σ' g (e.toIntertwiningMap v)
  rw [twist_apply, twist_apply, map_smul] at h1
  exact smul_right_injective V' (Units.ne_zero (χ g)) h1

theorem equiv_of_comp {σ : Representation ℂ G V} {σ' : Representation ℂ G V'} (θ : G →* G)
    (hθ : ∀ g, θ (θ g) = g) (e : Representation.Equiv (σ.comp θ : Representation ℂ G V) (σ'.comp θ : Representation ℂ G V')) :
    Nonempty (σ.Equiv σ') := by
  refine ⟨Representation.Equiv.mk e.toLinearEquiv fun g => LinearMap.ext fun v => ?_⟩
  have h1 := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap (θ g) v
  simp only [LinearMap.comp_apply]
  change e.toIntertwiningMap (σ g v) = σ' g (e.toIntertwiningMap v)
  simpa [MonoidHom.coe_comp, Function.comp_apply, hθ] using h1

end General

theorem exists_form_ne_zero {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {x : V ⊗[ℂ] W} (hx : x ≠ 0) :
    ∃ ℓ : V →ₗ[ℂ] ℂ, TensorProduct.lid ℂ W (TensorProduct.map ℓ LinearMap.id x) ≠ 0 := by
  let b := Module.Free.chooseBasis ℂ V
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := W) b
  have key : ∀ i (y : V ⊗[ℂ] W),
      TensorProduct.lid ℂ W (TensorProduct.map (b.coord i) LinearMap.id y) = e y i := by
    intro i y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v w =>
      simp [e, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
    | add y z hy hz => rw [map_add (f := _), map_add (f := _), hy, hz, map_add (f := _), Finsupp.add_apply]
  have hne : e x ≠ 0 := fun h => hx (e.injective (h.trans (map_zero e).symm))
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.1 hne
  exact ⟨b.coord i, by rw [key]; simpa using hi⟩

end GlobalTheory.HoweBridge

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct

namespace GlobalTheory.HoweBridge

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def invT (n : ℕ) : GL (Fin n) k →* GL (Fin n) k where
  toFun g := ⟨(g⁻¹).val.transpose, g.val.transpose,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' a b := by
    apply Units.ext
    simp only [Units.val_mul, mul_inv_rev, Matrix.transpose_mul]

theorem invT_invT (n : ℕ) (g : GL (Fin n) k) : invT n (invT n g) = g := by
  apply Units.ext
  show ((invT n g)⁻¹).val.transpose = g.val
  show (g.val.transpose).transpose = g.val
  rw [Matrix.transpose_transpose]

theorem continuous_invT (n : ℕ) : Continuous (invT (k := k) n) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

theorem uniq_left (hM : GlobalTheory.Published.MinguezThetaGL) (r n : ℕ) {V V' W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin r) k) V) (σ' : Representation ℂ (GL (Fin r) k) V')
    (τ : Representation ℂ (GL (Fin n) k) W) (hσ : IsSmooth σ) (hσi : σ.IsIrreducible)
    (hσ' : IsSmooth σ') (hσ'i : σ'.IsIrreducible) (hτ : IsSmooth τ) (hτi : τ.IsIrreducible)
    (h1 : OmQuot 1 σ τ) (h2 : OmQuot 1 σ' τ) : Nonempty (σ.Equiv σ') := by
  by_cases h0 : r = 0 ∨ n = 0
  · obtain ⟨⟨a⟩, -⟩ := GlobalTheory.T.om_quotient_trivial_rank_zero k r n V W σ τ h0 hσi hτi h1
    obtain ⟨⟨b⟩, -⟩ := GlobalTheory.T.om_quotient_trivial_rank_zero k r n V' W σ' τ h0 hσ'i hτi h2
    exact ⟨a.trans b.symm⟩
  · push_neg at h0
    obtain ⟨F, hF0, hF⟩ := h1
    obtain ⟨Φ₀, hΦ₀⟩ : ∃ Φ, F Φ ≠ 0 := by
      by_contra h
      push_neg at h
      exact hF0 (LinearMap.ext h)
    obtain ⟨ℓ, hℓ⟩ := exists_form_ne_zero hΦ₀
    let f : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W :=
      (TensorProduct.lid ℂ W).toLinearMap ∘ₗ TensorProduct.map ℓ LinearMap.id ∘ₗ F
    have hf0 : f ≠ 0 := fun h => hℓ (LinearMap.congr_fun h Φ₀)
    have hf : ∀ (h : GL (Fin n) k) (Φ Φ' : SB (Matrix (Fin n) (Fin r) k)),
        (Φ' : Matrix (Fin n) (Fin r) k → ℂ) = om 1 (1 : GL (Fin r) k) h Φ → f Φ' = τ h (f Φ) := by
      intro h Φ Φ' hΦ
      have e1 := hF 1 h Φ Φ' hΦ
      simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe, e1, map_one]
      generalize F Φ = x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul v w => simp
      | add y z hy hz => simp only [map_add (f := _), hy, hz]
    obtain ⟨V0, _, _, π', -, -, -, hU, -⟩ :=
      hM k n r (Nat.one_le_iff_ne_zero.2 h0.2) (Nat.one_le_iff_ne_zero.2 h0.1) W τ hτ hτi ⟨f, hf0, hf⟩
    obtain ⟨a⟩ := hU V σ hσ hσi ⟨F, hF0, hF⟩
    obtain ⟨b⟩ := hU V' σ' hσ' hσ'i h2
    exact ⟨a.trans b.symm⟩

end GlobalTheory.HoweBridge

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct

namespace GlobalTheory.HoweBridge

theorem main : GlobalTheory.Published.MinguezThetaGL → GlobalTheory.Published.HoweDualityGL := by
  intro hM k _ _ _ _ r n μ hμ
  have hr : IsSmoothChar (detChar (Fin r) μ⁻¹) := hμ.inv.detChar
  have hn : IsSmoothChar (detChar (Fin n) μ) := hμ.detChar
  refine ⟨?_, ?_⟩
  · intro V W W' _ _ _ _ _ _ σ τ τ' hσ hσi hτ hτi hτ' hτ'i h1 h2
    have h1' := (GlobalTheory.T.om_quotient_twist_det k r n μ V W σ τ).1 h1
    have h2' := (GlobalTheory.T.om_quotient_twist_det k r n μ V W' σ τ').1 h2
    have t1 := GlobalTheory.T.om_quotient_transpose_inverse k r n V W _ _ (invT r) (invT n) (fun _ => rfl) (fun _ => rfl) h1'
    have t2 := GlobalTheory.T.om_quotient_transpose_inverse k r n V W' _ _ (invT r) (invT n) (fun _ => rfl) (fun _ => rfl) h2'
    have hs : ∀ m : ℕ, Function.Surjective (invT (k := k) m) := fun m g => ⟨invT m g, invT_invT m g⟩
    obtain ⟨e⟩ := uniq_left hM n r _ _ _
      (isSmooth_comp (isSmooth_twist hτ hn) _ (continuous_invT n)) (irr_comp _ (hs n) (irr_twist hτi _))
      (isSmooth_comp (isSmooth_twist hτ' hn) _ (continuous_invT n)) (irr_comp _ (hs n) (irr_twist hτ'i _))
      (isSmooth_comp (isSmooth_twist hσ hr) _ (continuous_invT r)) (irr_comp _ (hs r) (irr_twist hσi _))
      t1 t2
    obtain ⟨e'⟩ := equiv_of_comp (invT n) (invT_invT n) e
    exact equiv_of_twist _ e'
  · intro V V' W _ _ _ _ _ _ σ σ' τ hσ hσi hσ' hσ'i hτ hτi h1 h2
    have h1' := (GlobalTheory.T.om_quotient_twist_det k r n μ V W σ τ).1 h1
    have h2' := (GlobalTheory.T.om_quotient_twist_det k r n μ V' W σ' τ).1 h2
    obtain ⟨e⟩ := uniq_left hM r n _ _ _
      (isSmooth_twist hσ hr) (irr_twist hσi _) (isSmooth_twist hσ' hr) (irr_twist hσ'i _)
      (isSmooth_twist hτ hn) (irr_twist hτi _) h1' h2'
    exact equiv_of_twist _ e

end GlobalTheory.HoweBridge
end
end
end
end

section

open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix

namespace GlobalTheory.InertCompletion


open scoped WithZeroTopology in
theorem exists_completion_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E))
    (h : IsInertAt F E v P) :
    ∃ φ : v.adicCompletion F →+* P.adicCompletion E, Continuous φ ∧
      (∀ x : F, φ (algebraMap F _ x) = algebraMap E _ (algebraMap F E x)) ∧
      ∀ x, Valued.v (φ x) = Valued.v x := by
  have h' : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal := h
  have : P.asIdeal.LiesOver v.asIdeal := ⟨v.isMaximal.eq_of_le
    (Ideal.comap_ne_top _ P.isPrime.ne_top) (h' ▸ Ideal.le_comap_map)⟩
  have he : Ideal.ramificationIdx' v.asIdeal P.asIdeal = 1 := by
    by_contra hne
    have := (Ideal.ramificationIdx'_ne_one_iff h'.le).1 hne
    rw [h'] at this
    exact absurd this (not_le_of_gt (Ideal.pow_lt_self _ P.ne_bot P.isPrime.ne_top 2 le_rfl))
  have hc := (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver F E v P).continuous
  let φ : v.adicCompletion F →+* P.adicCompletion E :=
    ((HeightOneSpectrum.adicCompletion.equiv E P).symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation F)) (WithVal (P.valuation E))) hc)).comp
      (HeightOneSpectrum.adicCompletion.equiv F v).toRingHom
  have hφ : ∀ x : F, φ (algebraMap F _ x) = algebraMap E _ (algebraMap F E x) := fun x => by
    apply HeightOneSpectrum.adicCompletion.ext
    exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ x)
  have hcont : Continuous φ :=
    (HeightOneSpectrum.adicCompletion.continuous_ofCompletion E P).comp
      ((UniformSpace.Completion.continuous_map
        (f := algebraMap (WithVal (v.valuation F)) (WithVal (P.valuation E)))).comp
        (HeightOneSpectrum.adicCompletion.continuous_toCompletion F v))
  refine ⟨φ, hcont, hφ, fun x => ?_⟩
  refine (HeightOneSpectrum.denseRange_algebraMap F v).induction_on
    (p := fun x => Valued.v (φ x) = Valued.v x) x
    (isClosed_eq
      ((Valued.continuous_valuation_of_surjective (P.valuedAdicCompletion_surjective E)).comp hcont)
      (Valued.continuous_valuation_of_surjective (v.valuedAdicCompletion_surjective F))) fun k => ?_
  rw [hφ, Idele.valued_algebraMap, Idele.valued_algebraMap,
    ← HeightOneSpectrum.valuation_liesOver E v P,
    ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal P.asIdeal v.ne_bot, he, pow_one]

theorem continuous_of_valued_eq {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    (σ : P.adicCompletion E →+* P.adicCompletion E) (h : ∀ x, Valued.v (σ x) = Valued.v x) :
    Continuous σ := by
  refine (AddMonoidHomClass.isometry_of_norm σ fun x => ?_).continuous
  exact le_antisymm (Valued.toNormedField.norm_le_iff.2 (h x).le) (Valued.toNormedField.norm_le_iff.2 (h x).ge)

theorem surjective_of_continuous {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E))
    (φ : v.adicCompletion F →+* P.adicCompletion E) (hc : Continuous φ)
    (ψ : v.adicCompletion F ⊗[F] E →+* P.adicCompletion E)
    (hψ : ∀ a x, ψ (a ⊗ₜ x) = φ a * algebraMap E _ x) : Function.Surjective ψ := by
  letI : Algebra (v.adicCompletion F) (P.adicCompletion E) := φ.toAlgebra
  haveI : ContinuousSMul (v.adicCompletion F) (P.adicCompletion E) :=
    continuousSMul_of_algebraMap _ _ hc
  letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _
  let f : v.adicCompletion F ⊗[F] E →ₐ[v.adicCompletion F] P.adicCompletion E :=
    ⟨ψ, fun a => (hψ a 1).trans (by rw [map_one, mul_one]; rfl)⟩
  have hcl : IsClosed (LinearMap.range f.toLinearMap : Set (P.adicCompletion E)) :=
    Submodule.closed_of_finiteDimensional _
  intro y
  refine (HeightOneSpectrum.denseRange_algebraMap E P).induction_on
    (p := fun y => y ∈ (LinearMap.range f.toLinearMap : Set (P.adicCompletion E))) y hcl fun x => ?_
  exact ⟨1 ⊗ₜ x, (hψ 1 x).trans (by rw [map_one, one_mul])⟩

theorem exists_ringEquiv_completion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (P : HeightOneSpectrum (𝓞 E)), IsInertAt (maximalRealSubfield E) E v P → ∀ σ : P.adicCompletion E →+* P.adicCompletion E, (∀ x : E, σ (algebraMap E (P.adicCompletion E) x) = algebraMap E (P.adicCompletion E) (ReciprocityTheory.ChartRestriction.G.FD.cc x)) → (∀ x, Valued.v (σ x) = Valued.v x) → ∃ ψ : LocAlg v ≃+* P.adicCompletion E, (∀ x : E, ψ (locEmb v x) = algebraMap E (P.adicCompletion E) x) ∧ (∀ z, ψ (locConj v z) = σ (ψ z)) ∧ ∀ z, z ∈ locOrder v ↔ Valued.v (ψ z) ≤ 1 := by
  intro E _ _ _ _ v P h σ hσ hσv
  obtain ⟨φ, hc, hφ, hv⟩ := exists_completion_map v P h
  obtain ⟨ψ, hψ⟩ : ∃ ψ : LocAlg v →+* P.adicCompletion E,
      ∀ a x, ψ (a ⊗ₜ x) = φ a * algebraMap E _ x := by
    letI : Algebra (maximalRealSubfield E) (P.adicCompletion E) :=
      ((algebraMap E (P.adicCompletion E)).comp (algebraMap (maximalRealSubfield E) E)).toAlgebra
    let f : E →ₐ[maximalRealSubfield E] P.adicCompletion E := ⟨algebraMap E _, fun _ => rfl⟩
    let g : v.adicCompletion (maximalRealSubfield E) →ₐ[maximalRealSubfield E] P.adicCompletion E :=
      ⟨φ, hφ⟩
    exact ⟨(Algebra.TensorProduct.productMap g f).toRingHom, fun a x => rfl⟩
  have hF : IsField (LocAlg v) := InertField.isField_of_inert _ E
    (Algebra.IsQuadraticExtension.finrank_eq_two _ E) v (by
      rw [show Ideal.map _ v.asIdeal = P.asIdeal from h]; exact P.isPrime)
  have hinj : Function.Injective ψ := by
    letI := hF.toField
    exact ψ.injective
  have hE : ∀ x : E, ψ (locEmb v x) = algebraMap E _ x := fun x =>
    (hψ 1 x).trans (by rw [map_one, one_mul])
  have hA : ∀ a, ψ (algebraMap _ (LocAlg v) a) = φ a := fun a =>
    (hψ a 1).trans (by rw [map_one, mul_one])
  have hσφ : ∀ a, σ (φ a) = φ a := fun a =>
    congrFun ((HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield E) v).equalizer
      ((continuous_of_valued_eq P σ hσv).comp hc) hc (funext fun x => by
        simp only [Function.comp_apply, hφ, hσ]
        exact congrArg _ ((IsCMField.complexConj E).commutes x))) a
  have hconj : ∀ z, ψ (locConj v z) = σ (ψ z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rw [locConj_tmul, hψ, hψ, map_mul, hσφ, hσ]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hint : ∀ s : 𝓞 E, Valued.v (algebraMap E (P.adicCompletion E) (s : E)) ≤ 1 := fun s =>
    (Idele.valued_algebraMap P (s : E)).trans_le (P.valuation_le_one s)
  refine ⟨RingEquiv.ofBijective ψ ⟨hinj, surjective_of_continuous v P φ hc ψ hψ⟩, hE, hconj,
    fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
  · change Valued.v (ψ z) ≤ 1
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact (congrArg Valued.v (hE a)).trans_le (hint a)
    | algebraMap a => exact ((congrArg Valued.v (hA a)).trans (hv a)).trans_le a.2
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Valuation.map_add_le _ hx hy
    | mul x y _ _ hx hy => rw [map_mul, map_mul]; exact mul_le_one' hx hy
  · replace hz : Valued.v (ψ z) ≤ 1 := hz
    have fix : ∀ w : LocAlg v, locConj v w = w → Valued.v (ψ w) ≤ 1 → w ∈ locOrder v := by
      intro w hw hw1
      obtain ⟨a, rfl⟩ := exists_of_locConj_eq v hw
      rw [hA, hv] at hw1
      exact (locOrder v).algebraMap_mem ⟨a, hw1⟩
    obtain ⟨θ, hθ⟩ := exists_sub_conj_notMem P.asIdeal P.isPrime.ne_top
    have hδ1 : P.valuation E ((θ : E) - ReciprocityTheory.ChartRestriction.G.FD.cc (θ : E)) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) P).2 hθ
    set δ : E := (θ : E) - ReciprocityTheory.ChartRestriction.G.FD.cc (θ : E) with hδ
    have hδ0 : δ ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hδ1
      exact zero_ne_one hδ1
    have hcδ : ReciprocityTheory.ChartRestriction.G.FD.cc δ⁻¹ = -δ⁻¹ := by
      have : ReciprocityTheory.ChartRestriction.G.FD.cc δ = -δ := by simp [hδ, ReciprocityTheory.ChartRestriction.G.FD.cc]
      rw [← inv_neg, ← this]
      exact map_inv₀ (IsCMField.complexConj E) δ
    have hone : locEmb v δ⁻¹ * (locEmb v θ - locEmb v (ReciprocityTheory.ChartRestriction.G.FD.cc (θ : E))) = 1 := by
      rw [← map_sub, ← map_mul, inv_mul_cancel₀ hδ0, map_one]
    set b : LocAlg v := (z - locConj v z) * locEmb v δ⁻¹ with hb
    have hb1 : locConj v b = b := by
      rw [hb, map_mul, map_sub, locConj_locConj, locConj_locEmb, hcδ, map_neg]; ring
    have hb2 : Valued.v (ψ b) ≤ 1 := by
      rw [hb, map_mul, map_mul, hE, Idele.valued_algebraMap, map_inv₀, hδ1, inv_one, mul_one,
        map_sub, hconj]
      exact Valuation.map_sub_le _ hz ((hσv _).trans_le hz)
    have ha1 : locConj v (z - b * locEmb v θ) = z - b * locEmb v θ := by
      rw [map_sub, map_mul, hb1, locConj_locEmb, hb]
      linear_combination (z - locConj v z) * hone
    have ha2 : Valued.v (ψ (z - b * locEmb v θ)) ≤ 1 := by
      rw [map_sub, map_mul, hE]
      refine Valuation.map_sub_le _ hz ?_
      rw [map_mul]
      exact mul_le_one' hb2 (hint θ)
    rw [← sub_add_cancel z (b * locEmb v θ)]
    exact add_mem (fix _ ha1 ha2) (mul_mem (fix _ hb1 hb2) (locEmb_mem_locOrder v θ))

end GlobalTheory.InertCompletion
end

section

open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix

namespace GlobalTheory.SelfDualGenus


open IsDedekindDomain NumberField in
open scoped TensorProduct Matrix in
theorem _root_.GlobalTheory.SelfDualGenus.isInertAt_of_unique_unramified (E : Type) [Field E] [NumberField E] [IsCMField E]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (P : HeightOneSpectrum (𝓞 E))
    (hP : ∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ (x : E)⁻¹ ∉ _root_.GlobalTheory.SelfDualGenus.semiLoc v))
    (hx : ∃ x : 𝓞 (maximalRealSubfield E), ∃ y : 𝓞 E,
      (y : E) = algebraMap (maximalRealSubfield E) E (x : maximalRealSubfield E) ∧
        y ∈ P.asIdeal ∧ y ∉ P.asIdeal ^ 2) :
    _root_.Formalism.UG.IsInertAt (maximalRealSubfield E) E v P := by
  unfold _root_.Formalism.UG.IsInertAt
  have key : ∀ P' : Ideal (𝓞 E), P'.IsMaximal →
      Ideal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) P' = v.asIdeal → P' ≤ P.asIdeal := by
    intro P' hP' hcomap z hz
    by_cases hz0 : z = 0
    · rw [hz0]; exact P.asIdeal.zero_mem
    rw [hP z hz0]
    intro hmem
    rw [_root_.GlobalTheory.SelfDualGenus.mem_semiLoc_iff] at hmem
    obtain ⟨t, ht, hint⟩ := hmem
    have hzE : (z : E) ≠ 0 := by exact_mod_cast hz0
    let w : 𝓞 E := ⟨_, hint⟩
    have hzw : z * w = algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) t := by
      apply NumberField.RingOfIntegers.ext
      show (z : E) * (((algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) t : 𝓞 E) : E) * (z : E)⁻¹) = _
      field_simp
    apply ht
    rw [← hcomap, Ideal.mem_comap, ← hzw]
    exact P'.mul_mem_right _ hz
  have hker : RingHom.ker (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ≤ v.asIdeal := by
    intro a ha
    rw [RingHom.mem_ker] at ha
    have ha0 : a = 0 := FaithfulSMul.algebraMap_injective (𝓞 (maximalRealSubfield E)) (𝓞 E)
      (by rw [ha, map_zero])
    rw [ha0]; exact v.asIdeal.zero_mem
  obtain ⟨P0, hP0, hP0c⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral v.asIdeal hker
  have hP0P : P0 = P.asIdeal := hP0.eq_of_le P.isPrime.ne_top (key P0 hP0 hP0c)
  have hcP : Ideal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) P.asIdeal = v.asIdeal := by
    rw [← hP0P]
    exact hP0c
  have hQP : Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal ≤ P.asIdeal := by
    rw [Ideal.map_le_iff_le_comap, hcP]
  obtain ⟨x, y, hyx, hyP, hyP2⟩ := hx
  have hyx' : y = algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) x := by
    apply NumberField.RingOfIntegers.ext
    rw [hyx]
    rfl
  have hxv : x ∈ v.asIdeal := by
    rw [← hcP, Ideal.mem_comap, ← hyx']; exact hyP
  have hyQ : y ∈ Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal := by
    rw [hyx']; exact Ideal.mem_map_of_mem _ hxv
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hQP
  by_cases hJtop : J = ⊤
  · rw [hJ, hJtop, Ideal.mul_top]
  exfalso
  obtain ⟨P'', hP'', hJP''⟩ := Ideal.exists_le_maximal J hJtop
  have hQP'' : Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal ≤ P'' := by
    rw [hJ]; exact Ideal.mul_le_right.trans hJP''
  have hcP'' : Ideal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) P'' = v.asIdeal := by
    refine (v.isMaximal.eq_of_le (Ideal.comap_ne_top _ hP''.ne_top) ?_).symm
    rw [← Ideal.map_le_iff_le_comap]; exact hQP''
  have hJP : J ≤ P.asIdeal := hJP''.trans (key P'' hP'' hcP'')
  apply hyP2
  rw [pow_two]
  have := hJ ▸ hyQ
  exact Ideal.mul_mono_right hJP this

end GlobalTheory.SelfDualGenus
end

section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.finiteDimensional_of_finite_subring_hom_of_fractions : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (B : Subring K) (B' : Subring L) (φ : B →+* B'), (∀ x : B, (φ x : L) = algebraMap K L x) → φ.Finite → (∀ y : L, ∃ a ∈ B', ∃ b ∈ B', b ≠ 0 ∧ y * b = a) → FiniteDimensional K L := by
  first | (exact @GlobalTheory.finiteDimensional_of_finite_subring_fraction) | (exact GlobalTheory.finiteDimensional_of_finite_subring_fraction) | (intros; apply GlobalTheory.finiteDimensional_of_finite_subring_fraction  <;> assumption)
end
