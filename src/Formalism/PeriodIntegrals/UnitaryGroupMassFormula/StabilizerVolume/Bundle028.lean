module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle027
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle006
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoGram
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.Automorphisms.Bundle001
public import ReciprocityTheory.ResidueCardinality.ArtinOntoB
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace PI.VolStabS.TopoMuInv

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix NumberField IsDedekindDomain
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [SecondCountableTopology R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem smul_apply (h : HA R σ J) {n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) (x : Fin n) :
    (h • X) x = ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) *ᵥ X x :=
  rfl

theorem BR_smul (h : HA R σ J) {n : ℕ} (X Y : Fin n → Fin M → R ⊗[F] E) :
    BR R σ J (h • X) (h • Y) = BR R σ J X Y := by
  have hg' : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ) ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) _) * JR R J *
      ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) = JR R J := h.2
  simp only [BR, smul_apply, hR, TopoGram.hform_mulVec, hg']

theorem BR_smul_left (h : HA R σ J) {n : ℕ} (X Y : Fin n → Fin M → R ⊗[F] E) :
    BR R σ J (h • X) Y = BR R σ J X (h⁻¹ • Y) := by
  conv_lhs => rw [← smul_inv_smul h Y]
  exact BR_smul R σ J h X (h⁻¹ • Y)

theorem smul_neg' (h : HA R σ J) {n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) :
    h • (-X) = -(h • X) := by
  funext x
  simp only [smul_apply, Pi.neg_apply, mulVec_neg]

def smulAddEquiv (h : HA R σ J) (n : ℕ) :
    (Fin n → Fin M → R ⊗[F] E) ≃+ (Fin n → Fin M → R ⊗[F] E) where
  toEquiv := MulAction.toPerm h
  map_add' X Y := by
    funext x
    change ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) _) *ᵥ (X x + Y x) = _
    rw [mulVec_add]
    rfl

theorem selfDual_map (ψR : R → ℂ) {n : ℕ} (μ : Measure (Fin n → Fin M → R ⊗[F] E))
    (hμ : SdW F E σ M J R ψR n μ) (h : HA R σ J) :
    SdW F E σ M J R ψR n (μ.map (fun X => h • X)) := by
  let e := PI.VolStabS.smulHomeo R σ (a := n) J h
  let em := e.toMeasurableEquiv
  have hmap : μ.map (fun X => h • X) = μ.map em := rfl
  have : μ.IsAddHaarMeasure := hμ.1
  refine ⟨?_, fun Φ hc hcs hI z => ?_⟩
  · exact (smulAddEquiv R σ J h n).isAddHaarMeasure_map μ e.continuous e.symm.continuous
  rw [hmap] at hI ⊢
  let Fh : (Fin n → Fin M → R ⊗[F] E) → ℂ := fun w =>
    ∫ x, Φ (h • x) * ψR (BR R σ J x w) ∂μ
  have hin : ∀ y, ∫ x, Φ x * ψR (BR R σ J x y) ∂(μ.map em) = Fh (h⁻¹ • y) := fun y => by
    rw [integral_map_equiv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show Φ (h • x) * ψR (BR R σ J (h • x) y) = Φ (h • x) * ψR (BR R σ J x (h⁻¹ • y))
    rw [BR_smul_left]
  have hI' : Integrable Fh μ := by
    rw [integrable_map_equiv] at hI
    refine hI.congr (Filter.Eventually.of_forall fun y => ?_)
    show ∫ x, Φ x * ψR (BR R σ J x (h • y)) ∂(μ.map em) = Fh y
    rw [hin, inv_smul_smul]
  have key := hμ.2 (fun x => Φ (h • x)) (hc.comp e.continuous) (hcs.comp_homeomorph e) hI'
    (h⁻¹ • z)
  rw [integral_map_equiv]
  have e3 : (fun y => (∫ x, Φ x * ψR (BR R σ J x (em y)) ∂(μ.map em)) *
      ψR (BR R σ J (em y) z)) = fun y => Fh y * ψR (BR R σ J y (h⁻¹ • z)) := by
    funext y
    show (∫ x, Φ x * ψR (BR R σ J x (h • y)) ∂(μ.map em)) * ψR (BR R σ J (h • y) z) = _
    rw [hin, inv_smul_smul, BR_smul_left]
  rw [e3]
  refine key.trans ?_
  show Φ (h • -(h⁻¹ • z)) = Φ (-z)
  rw [smul_neg', smul_inv_smul]

end PI.VolStabS.TopoMuInv

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

theorem muInvInf_of (hU : SdUniq) : MuInvInf := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μinf hμ h
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  exact (hU F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ).1 _ _
    (TopoMuInv.selfDual_map (Ainf F) σ J (psiInf F ψ) μinf hμ h) hμ

theorem muInvV_of (hU : SdUniq) : MuInvV := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ v μv hμ h
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  exact ((hU F E σ hCM M J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ).2.2 v).1 _ _
    (TopoMuInv.selfDual_map (Fv F v) σ J (psiV F ψ v) μv hμ h) hμ

theorem nuInv_of_pin (hD : DetAdm) (hC : CompG) (hP : FibPin) (hU : SdUniq) : NuInv :=
  nuInv_of_steps hD hC hP (muInvInf_of hU) (muInvV_of hU)

end PI.VolStabS
end
end

section

noncomputable section

namespace PI.VolStabS

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  IsLocalRing

namespace IdxHW

section Comap

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (b : Module.Basis (Fin 2) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ)

theorem val_mul_lt {x y : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) (hy : Valued.v y < 1) :
    Valued.v (x * y) < 1 := by
  have hx' : Valued.v x ≤ 1 := hx
  calc Valued.v (x * y) = Valued.v x * Valued.v y := map_mul _ _ _
    _ ≤ 1 * Valued.v y := by gcongr
    _ = Valued.v y := one_mul _
    _ < 1 := hy

theorem comap_eq (k0 k1 : Fin 2) (hk : k0 ≠ k1) (ρ : F)
    (hC : ∀ k l, algebraMap F (Fv F v) (Cmat b σ k l) ∈ v.adicCompletionIntegers F)
    (hρ : algebraMap F (Fv F v) ρ ∈ v.adicCompletionIntegers F)
    (hfix : ∀ x : Fin 2 → Fv F v,
      Matrix.mulVec ((Cmat b σ).map (algebraMap F (Fv F v))) x = x →
        x k1 = algebraMap F (Fv F v) ρ * x k0) :
    (hF b v σ a 0).addSubgroupOf (hermO b v σ a) =
      (AddSubgroup.pi Set.univ fun _ : Fin a × Fin a =>
        (maximalIdeal (v.adicCompletionIntegers F)).toAddSubgroup).comap (psi b v σ a k0) := by
  rw [← ker_redH]
  ext S
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_comap, AddSubgroup.mem_pi]
  have key : redH b v σ a S = 0 ↔ ∀ i j k, Valued.v (crdS b v σ a S i j k) < 1 := by
    constructor
    · intro h i j k
      have h1 : residue _ (⟨crdS b v σ a S i j k, (mem_hermO_iff b v σ a S).1 S.2 i j k⟩ :
          v.adicCompletionIntegers F) = 0 := congrFun (congrFun (congrFun h i) j) k
      have h2 := (ReciprocityTheory.Aut.mem_maxIdeal_iff v _).1 ((residue_eq_zero_iff _).1 h1)
      exact h2
    · intro h
      funext i j k
      have h3 := res_of_val v ⟨crdS b v σ a S i j k, (mem_hermO_iff b v σ a S).1 S.2 i j k⟩ (h i j k)
      exact h3
  rw [key]
  set Sm : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) :=
    ((S : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) with hSm
  have hps : ∀ q, psi b v σ a k0 S q ∈ (maximalIdeal (v.adicCompletionIntegers F)).toAddSubgroup ↔
      Valued.v ((psi b v σ a k0 S q : v.adicCompletionIntegers F) : Fv F v) < 1 :=
    fun q => ReciprocityTheory.Aut.mem_maxIdeal_iff v _
  constructor
  · intro h q _
    rw [hps]
    obtain ⟨i, j⟩ := q
    rcases lt_trichotomy i j with hij | hij | hij
    · simp only [psi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, if_pos hij]
      exact h i j 0
    · subst hij
      simp only [psi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, lt_irrefl, if_false]
      exact h i i k0
    · simp only [psi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, if_neg (not_lt.2 hij.le), if_pos hij]
      exact h j i 1
  · intro h
    have h' : ∀ q, Valued.v ((psi b v σ a k0 S q : v.adicCompletionIntegers F) : Fv F v) < 1 :=
      fun q => (hps q).1 (h q (Set.mem_univ q))
    have hup : ∀ i j, i < j → ∀ k, Valued.v (crdS b v σ a S i j k) < 1 := by
      intro i j hij k
      fin_cases k
      · have := h' (i, j)
        simp only [psi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, if_pos hij] at this
        exact this
      · have := h' (j, i)
        simp only [psi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, if_neg (not_lt.2 hij.le),
          if_pos hij] at this
        exact this
    intro i j k
    rcases lt_trichotomy i j with hij | hij | hij
    · exact hup i j hij k
    · subst hij
      have hd : Valued.v (crdS b v σ a S i i k0) < 1 := by
        have := h' (i, i)
        simp only [psi, AddMonoidHom.coe_mk, ZeroHom.coe_mk, lt_irrefl, if_false] at this
        exact this
      have hfx := hfix (fun l => crdS b v σ a S i i l) (by
        funext m
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
        have hs : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (Sm i i) = Sm i i := S.1.2 i i
        have := cr_sig b v σ (Sm i i) m
        rw [hs] at this
        simp only [crdS_eq]
        exact this.symm)
      have hkk : k = k0 ∨ k = k1 := by
        fin_cases k <;> fin_cases k0 <;> fin_cases k1 <;> simp_all
      rcases hkk with rfl | rfl
      · exact hd
      · have e : crdS b v σ a S i i k = algebraMap F (Fv F v) ρ * crdS b v σ a S i i k0 := hfx
        rw [e]
        exact val_mul_lt v hρ hd
    · have hs : Sm i j = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (Sm j i) := (S.1.2 i j).symm
      rw [crdS_eq, show ((S : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = Sm i j
        from rfl, hs, cr_sig, Fin.sum_univ_two]
      refine Valuation.map_add_lt _ (val_mul_lt v (hC _ _) ?_) (val_mul_lt v (hC _ _) ?_)
      · exact hup j i hij 0
      · exact hup j i hij 1

end Comap

theorem index_max {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    (maximalIdeal (v.adicCompletionIntegers F)).toAddSubgroup.index = Nat.card (𝓞 F ⧸ v.asIdeal) := by
  rw [← ReciprocityTheory.Bridge.ResidueFieldCardinality.card_residue v]
  rfl

end IdxHW

end PI.VolStabS
end
end

section

noncomputable section

namespace PI.VolStabS

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  IsLocalRing

namespace IdxHW

section Surj

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (b : Module.Basis (Fin 2) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ)

theorem psi_surj (k0 : Fin 2) (hσ : ∀ x, σ (σ x) = x)
    (hC : ∀ k l, algebraMap F (Fv F v) (Cmat b σ k l) ∈ v.adicCompletionIntegers F)
    (hu : ∀ k, algebraMap F (Fv F v) (b.repr 1 k / b.repr 1 k0) ∈ v.adicCompletionIntegers F)
    (hk0 : b.repr 1 k0 ≠ 0) : Function.Surjective (psi b v σ a k0) := by
  intro g
  have hinv : ∀ y : Fv F v ⊗[F] E, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ y) = y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, hσ]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  set u : Fv F v := algebraMap F (Fv F v) (b.repr 1 k0) with hu_def
  have hu0 : u ≠ 0 := (map_ne_zero (algebraMap F (Fv F v))).mpr hk0
  let Y : Fin a → Fin a → Fv F v ⊗[F] E := fun i j =>
    (Algebra.TensorProduct.basis (Fv F v) b).equivFun.symm ![(g (i, j) : Fv F v), (g (j, i) : Fv F v)]
  let D : Fin a → Fv F v ⊗[F] E := fun i => ((g (i, i) : Fv F v) / u) • (1 : Fv F v ⊗[F] E)
  let M : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E) := fun i j =>
    if i < j then Y i j else if j < i then Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (Y j i) else D i
  have hD : ∀ i, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (D i) = D i := by
    intro i
    simp [D, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
  have hY : ∀ i j k, cr b v (Y i j) k = ![(g (i, j) : Fv F v), (g (j, i) : Fv F v)] k :=
    fun i j k => cr_symm b v _ k
  have hDk : ∀ i k, cr b v (D i) k = (g (i, i) : Fv F v) / u * algebraMap F (Fv F v) (b.repr 1 k) :=
    fun i k => cr_smul_one b v _ k
  have hM : M ∈ HermR (Fv F v) σ a := by
    show ∀ i j, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (M j i) = M i j
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [M, h, lt_asymm h, hinv]
    · simp [M, hD]
    · simp [M, h, lt_asymm h]
  have hO : (⟨M, hM⟩ : HermR (Fv F v) σ a) ∈ hermO b v σ a := by
    rw [mem_hermO_iff]
    intro i j k
    rw [crdS_eq]
    show cr b v (M i j) k ∈ _
    rcases lt_trichotomy i j with h | rfl | h
    · simp only [M, if_pos h]
      rw [hY]
      fin_cases k <;> simp
    · simp only [M, lt_irrefl, if_false]
      rw [hDk]
      have e : (g (i, i) : Fv F v) / u * algebraMap F (Fv F v) (b.repr 1 k)
          = (g (i, i) : Fv F v) * algebraMap F (Fv F v) (b.repr 1 k / b.repr 1 k0) := by
        rw [map_div₀, ← hu_def]
        ring
      rw [e]
      exact mul_mem (g _).2 (hu k)
    · simp only [M, if_neg (lt_asymm h), if_pos h]
      rw [cr_sig]
      refine sum_mem fun l _ => mul_mem (hC k l) ?_
      rw [hY]
      fin_cases l <;> simp
  refine ⟨⟨⟨M, hM⟩, hO⟩, ?_⟩
  funext q
  obtain ⟨i, j⟩ := q
  simp only [psi, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  split_ifs with h1 h2
  · apply Subtype.ext
    show cr b v (M i j) 0 = _
    simp only [M, if_pos h1]
    rw [hY]
    simp
  · apply Subtype.ext
    show cr b v (M j i) 1 = _
    simp only [M, if_pos h2]
    rw [hY]
    simp
  · have hij : i = j := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
    subst hij
    apply Subtype.ext
    show cr b v (M i i) k0 = _
    simp only [M, lt_irrefl, if_false]
    rw [hDk, ← hu_def]
    exact div_mul_cancel₀ _ hu0

end Surj

end IdxHW

end PI.VolStabS
end
end
