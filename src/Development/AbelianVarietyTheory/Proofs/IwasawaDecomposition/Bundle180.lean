module

public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle167
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle159
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle035
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalUnfoldingNonvanishingIffEventuallyNonzero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle080
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle174
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle165
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle171
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDerivative.ExistsOePerm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle175
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.InfGroup

section General

variable {S : Type} [CommRing S] {I : Type} {M : ℕ}

def lift (e : S ≃+* (I → ℂ)) (m : I → Matrix (Fin M) (Fin M) ℂ) : Matrix (Fin M) (Fin M) S :=
  Matrix.of fun a b => e.symm fun i => m i a b

variable {e : S ≃+* (I → ℂ)} {θ : I → (S →+* ℂ)}

theorem lift_map (he : ∀ x i, e x i = θ i x) (m : I → Matrix (Fin M) (Fin M) ℂ) (i : I) :
    (lift e m).map (θ i) = m i := by
  ext a b
  simp [lift, ← he]

theorem ext_map (he : ∀ x i, e x i = θ i x) {X Y : Matrix (Fin M) (Fin M) S}
    (h : ∀ i, X.map (θ i) = Y.map (θ i)) : X = Y := by
  ext a b
  apply e.injective
  funext i
  rw [he, he]
  exact congrFun (congrFun (h i) a) b

theorem cT_map {s : S →+* S} {t : S →+* ℂ} (hs : ∀ x, t (s x) = star (t x))
    (X : Matrix (Fin M) (Fin M) S) : (Formalism.UG.cT s X).map t = (X.map t)ᴴ := by
  ext a b
  simp [Formalism.UG.cT, hs]

theorem conj_mul {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] {A : Matrix m n ℂ}
    {B : Matrix n m ℂ} (hBA : B * A = 1) (X Y : Matrix n n ℂ) :
    A * X * B * (A * Y * B) = A * (X * Y) * B := by
  calc A * X * B * (A * Y * B) = A * X * (B * A) * Y * B := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hBA]; simp only [Matrix.mul_assoc, Matrix.mul_one]

theorem conj_conj {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] {A : Matrix m n ℂ}
    {B : Matrix n m ℂ} (hBA : B * A = 1) (X : Matrix n n ℂ) :
    B * (A * X * B) * A = X := by
  calc B * (A * X * B) * A = (B * A) * X * (B * A) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hBA]; simp

theorem conj_unitary {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] {A : Matrix m n ℂ}
    {B : Matrix n m ℂ} (hBA : B * A = 1) {G X : Matrix n n ℂ} {K : Matrix m m ℂ}
    (hK : Bᴴ * G * B = K) (hX : Xᴴ * G * X = G) :
    (A * X * B)ᴴ * K * (A * X * B) = K := by
  rw [← hK]
  calc (A * X * B)ᴴ * (Bᴴ * G * B) * (A * X * B)
      = Bᴴ * (Xᴴ * ((B * A)ᴴ * G * (B * A)) * X) * B := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [hBA, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hX]

theorem exists_equiv [TopologicalSpace S] (he : ∀ x i, e x i = θ i x) (hc : Continuous e)
    (hc' : Continuous e.symm) (s : S →+* S) (hs : ∀ x i, θ i (s x) = star (θ i x))
    (J : Matrix (Fin M) (Fin M) S) (P Q : I → ℕ)
    (A : ∀ i, Matrix (Fin (P i) ⊕ Fin (Q i)) (Fin M) ℂ)
    (B : ∀ i, Matrix (Fin M) (Fin (P i) ⊕ Fin (Q i)) ℂ)
    (hAB : ∀ i, A i * B i = 1) (hBA : ∀ i, B i * A i = 1)
    (hA : ∀ i, (A i)ᴴ * Formalism.UG.Jpq (P i) (Q i) * A i = J.map (θ i)) :
    ∃ f : Formalism.UG.UJ s J ≃ₜ* (∀ i, UpqT (P i) (Q i)), ∀ h i, UpqT.mat (f h i) * A i =
      A i * ((h.1 : GL (Fin M) S) : Matrix (Fin M) (Fin M) S).map (θ i) := by
  have hB : ∀ i, (B i)ᴴ * J.map (θ i) * B i = Formalism.UG.Jpq (P i) (Q i) := by
    intro i
    rw [← hA]
    calc (B i)ᴴ * ((A i)ᴴ * Formalism.UG.Jpq (P i) (Q i) * A i) * B i
        = (A i * B i)ᴴ * Formalism.UG.Jpq (P i) (Q i) * (A i * B i) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hAB]; simp
  have hone : ∀ i, (1 : Matrix (Fin M) (Fin M) S).map (θ i) = 1 := fun i =>
    Matrix.map_one _ (map_zero _) (map_one _)
  have hθ : ∀ i, Continuous (θ i) := fun i => by
    have : (θ i : S → ℂ) = fun x => e x i := funext fun x => (he x i).symm
    rw [this]
    exact (continuous_apply i).comp hc
  have hfw : ∀ (h : Formalism.UG.UJ s J) (i : I), ∃ g : UpqT (P i) (Q i),
      UpqT.mat g = A i * h.1.1.map (θ i) * B i := by
    intro h i
    have hh : Formalism.UG.cT s h.1.1 * J * h.1.1 = J := h.2
    have h2 := congrArg (fun X => Matrix.map X (θ i)) hh
    simp only [Matrix.map_mul, cT_map (fun x => hs x i)] at h2
    have : A i * h.1.1.map (θ i) * B i ∈ Set.range (UpqT.mat (P := P i) (Q := Q i)) := by
      rw [GlobalTheory.UpqTopology.range_mat]
      exact conj_unitary (hBA i) (hB i) h2
    exact this
  choose fw hfw using hfw
  have hmul : ∀ {p q : ℕ} (a b : UpqT p q), UpqT.mat (a * b) = UpqT.mat a * UpqT.mat b :=
    fun _ _ => rfl
  have hm1 : ∀ {p q : ℕ}, UpqT.mat (1 : UpqT p q) = 1 := rfl
  have hinj : ∀ (p q : ℕ), Function.Injective (UpqT.mat (P := p) (Q := q)) :=
    fun _ _ => GlobalTheory.UpqTopology.isClosedEmbedding_mat.injective
  let L : (∀ i, UpqT (P i) (Q i)) → Matrix (Fin M) (Fin M) S :=
    fun g => lift e fun i => B i * UpqT.mat (g i) * A i
  have hL : ∀ g i, (L g).map (θ i) = B i * UpqT.mat (g i) * A i := fun g i => lift_map he _ i
  have hLmul : ∀ g g', L g * L g' = L (g * g') := by
    intro g g'
    refine ext_map he fun i => ?_
    rw [Matrix.map_mul, hL, hL, hL, conj_mul (hAB i), Pi.mul_apply, hmul]
  have hL1 : L 1 = 1 := by
    refine ext_map he fun i => ?_
    rw [hL, Pi.one_apply, hm1, Matrix.mul_one, hBA, hone]
  have hLu : ∀ g, Formalism.UG.cT s (L g) * J * L g = J := by
    intro g
    refine ext_map he fun i => ?_
    rw [Matrix.map_mul, Matrix.map_mul, cT_map (fun x => hs x i), hL]
    exact conj_unitary (hAB i) (hA i) (GlobalTheory.UpqTopology.mat_unitary (g i))
  have hLc : Continuous L := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    refine hc'.comp (continuous_pi fun i => ?_)
    have : Continuous fun g : ∀ i, UpqT (P i) (Q i) => B i * UpqT.mat (g i) * A i :=
      (continuous_const.matrix_mul
        (GlobalTheory.UpqTopology.continuous_mat.comp (continuous_apply i))).matrix_mul continuous_const
    exact this.matrix_elem a b
  let bw : (∀ i, UpqT (P i) (Q i)) → Formalism.UG.UJ s J := fun g =>
    ⟨⟨L g, L g⁻¹, by rw [hLmul, mul_inv_cancel, hL1], by rw [hLmul, inv_mul_cancel, hL1]⟩, hLu g⟩
  haveI : ∀ i, IsTopologicalGroup (UpqT (P i) (Q i)) := fun i => (GlobalTheory.UpqTopology.upq_lcsc _ _).1
  refine ⟨
    { toFun := fw
      invFun := bw
      left_inv := fun h => ?_
      right_inv := fun g => ?_
      map_mul' := fun h h' => ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }, fun h i => ?_⟩
  · refine Subtype.ext (Units.ext (ext_map he fun i => ?_))
    change (L (fw h)).map (θ i) = _
    rw [hL, hfw, conj_conj (hBA i)]
  · funext i
    apply hinj
    rw [hfw]
    change A i * (L g).map (θ i) * B i = _
    rw [hL, conj_conj (hAB i)]
  · funext i
    apply hinj
    rw [Pi.mul_apply, hmul, hfw, hfw, hfw, conj_mul (hBA i), ← Matrix.map_mul]
    rfl
  · refine continuous_pi fun i => GlobalTheory.UpqTopology.isInducing_mat.continuous_iff.2 ?_
    have : (UpqT.mat ∘ fun h => fw h i) = fun h : Formalism.UG.UJ s J => A i * h.1.1.map (θ i) * B i :=
      funext fun h => hfw h i
    rw [this]
    exact (continuous_const.matrix_mul ((Units.continuous_val.comp continuous_subtype_val).matrix_map
      (hθ i))).matrix_mul continuous_const
  · refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨hLc, hLc.comp continuous_inv⟩) _
  · change UpqT.mat (fw h i) * A i = _
    rw [hfw, Matrix.mul_assoc, hBA, Matrix.mul_one]

end General

theorem real_points : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (θ : I → (Ainf F ⊗[F] E →+* ℂ)) (P Q : I → ℕ) (A : ∀ i, Matrix (Fin (P i) ⊕ Fin (Q i)) (Fin M) ℂ), IsCMExt F E σ → IsCMFam τ → (∀ i, IsInfEmb (τ i) (θ i)) → (∀ i, Formalism.UG.HasSignature (J.map (τ i)) (P i) (Q i)) → (∀ i, (A i)ᴴ * Formalism.UG.Jpq (P i) (Q i) * A i = J.map (τ i)) → ∃ e : HA (Ainf F) σ J ≃ₜ* (∀ i, UpqT (P i) (Q i)), ∀ h i, UpqT.mat (e h i) * A i = A i * ((HA.mat (Ainf F) σ J h : GL (Fin M) (Ainf F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E)).map (θ i) := by
  intro F E _ _ _ _ _ σ M J I _ τ θ P Q A hcm hfam hθ hsig hA
  obtain ⟨e, he, hc, hc', hs⟩ := GlobalTheory.T.exists_archAdeleTensor_equiv_complex_cmType F E σ I τ θ hcm hfam hθ
  choose B hAB hBA using fun i =>
    (GlobalTheory.Mem.SignatureFactor.exists_factor M (P i) (Q i) _ (hsig i)).2.2 (A i) (hA i)
  refine exists_equiv he hc hc' (sigR (Ainf F) σ) (fun x i => by rw [← he, ← he, hs])
    (JR (Ainf F) J) P Q A B hAB hBA fun i => ?_
  rw [hA]
  ext a b
  exact ((hθ i).1 (J a b)).symm

end GlobalTheory.Mem.InfGroup
end
end

section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem _root_.GlobalTheory.T.notMem_support_ker_mulSection_of_nonvanishing : ∀ {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (s : L.Sec) (G : Y.Modules) [G.IsQuasicoherent], ∀ x ∈ Out.nonzeroLocus s, x ∉ support (kernel (cutHom G hL s)) := by
  first | exact @GlobalTheory.KernelCut.notMem_support_kernel_cutHom | exact GlobalTheory.KernelCut.notMem_support_kernel_cutHom | (intros; apply GlobalTheory.KernelCut.notMem_support_kernel_cutHom <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

namespace SerreCriterion

variable {X : Scheme.{0}}

theorem exists_germ_eq_of_support_subset {F : X.Modules} {y : X} (hy : IsClosed ({y} : Set X))
    (hF : support F ⊆ {y}) (t : (F.presheaf.stalk y :)) :
    ∃ s : Γ(F, ⊤), F.presheaf.germ ⊤ y trivial s = t := by
  classical
  by_cases h : y ∈ support F
  · obtain ⟨s, hs⟩ := (germ_support_bijective (F := F) ((Set.finite_singleton y).subset hF)
      fun x hx => by rw [show x = y from hF hx]; exact hy).2
      (Function.update (fun _ => 0) ⟨y, h⟩ t)
    refine ⟨s, (congrFun hs ⟨y, h⟩).trans ?_⟩
    simp
  · exact ⟨0, (notMem_support_iff.1 h).elim _ _⟩

theorem support_pushforward_subscheme_subset (Y : X.IdealSheafData) :
    support ((Scheme.Modules.pushforward Y.subschemeι).obj (structureModule Y.subscheme)) ⊆
      Y.support := by
  intro x hx
  by_contra h
  refine notMem_support_iff.2 (subsingleton_of_forall_eq 0 fun t => ?_) hx
  obtain ⟨V, hV, hxV, s, rfl⟩ := exists_germ_eq_of_mem (U := Y.support.compl) h t
  have e : Y.subschemeι ⁻¹ᵁ V = ⊥ :=
    eq_bot_iff.2 fun z hz => (hV hz (Y.range_subschemeι.le ⟨z, rfl⟩)).elim
  have : Subsingleton Γ(Y.subscheme, Y.subschemeι ⁻¹ᵁ V) := by
    rw [e]
    infer_instance
  have hs : s = 0 := this.elim s 0
  rw [hs, map_zero]

theorem not_isUnit_of_toSubscheme_eq_zero (Y : X.IdealSheafData) {y : X} (hy : y ∈ Y.support)
    (g : ((structureModule X).presheaf.stalk y :)) (hg : stalkLinear (toSubscheme Y) y g = 0) :
    ¬ IsUnit (structureModuleStalkEquiv y g) := by
  have hex := (exact_iff_stalkLinear (ShortComplex.mk (kernel.ι (toSubscheme Y)) (toSubscheme Y)
    (kernel.condition _))).1 (ShortComplex.exact_kernel _) y
  obtain ⟨u, rfl⟩ := (hex g).1 hg
  obtain ⟨V, hV, u, rfl⟩ := (idealModule Y).presheaf.exists_germ_eq u
  intro hu
  refine notMem_support_of_mem_basicOpen Y u ((X.mem_basicOpen _ y hV).2 ?_) hy
  rw [← structureModuleStalkEquiv_germ, ← stalkLinear_germ]
  exact hu

theorem exists_mem_nonzeroLocus {M : LB X} (hM : M.IsLB) {J : X.Modules}
    (j : J ⟶ structureModule X) (Y : X.IdealSheafData) {y : X} (hY : (Y.support : Set X) = {y})
    (h : Subsingleton (coh (twist (kernel (j ≫ toSubscheme Y)) M) 1))
    {U : X.Opens} (hU : y ∈ U) (t : Γ(J, U))
    (ht : structureModuleSectionsEquiv U (j.app U t) = 1) :
    ∃ a : Γ(twist J M, ⊤), y ∈ nonzeroLocus (secOfTwist j a) := by
  set φ := j ≫ toSubscheme Y with hφ
  let S : ShortComplex X.Modules :=
    ShortComplex.mk (kernel.ι φ) (cokernel.π (kernel.ι φ)) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  have hS' : (S.map (twistFunctor M)).ShortExact := Twist.shortExact_map hM hS
  have hsurj := cohOn.app_surjective hS' ⊤ h
  have hyc : IsClosed ({y} : Set X) := hY ▸ Y.support.isClosed
  have hQ : support (twist S.X₃ M) ⊆ {y} := by
    rw [support_twist hM, ← hY]
    refine fun x hx => support_pushforward_subscheme_subset Y ?_
    have := mem_support_iff.1 hx
    exact mem_support_iff.2 (stalkLinear_injective (Abelian.factorThruCoimage φ) x).nontrivial
  obtain ⟨c, hc⟩ := exists_chart hM y
  obtain ⟨b, hb⟩ := exists_germ_eq_of_support_subset hyc hQ
    ((stalkEquiv S.X₃ hM c hc).symm (stalkLinear S.g y (J.presheaf.germ U y hU t)))
  obtain ⟨a, rfl⟩ := hsurj b
  refine ⟨a, basicOpen_le_nonzeroLocus _ c ((X.mem_basicOpen _ y hc).2 ?_)⟩
  have hm : y ∈ ⊤ ⊓ M.U c := ⟨trivial, hc⟩
  replace hb := (stalkEquiv_germ hM c hc (V := ⊤) trivial _).symm.trans
    ((LinearEquiv.eq_symm_apply _).1 hb)
  have h₁ : stalkLinear S.g y (J.presheaf.germ _ y hm (coord (F := J) a c)) =
      stalkLinear S.g y (J.presheaf.germ U y hU t) :=
    (stalkLinear_germ S.g y hm _).trans hb
  have h₂ : stalkLinear φ y (J.presheaf.germ U y hU t -
      J.presheaf.germ _ y hm (coord (F := J) a c)) = 0 := by
    rw [← Abelian.coimage.fac φ, stalkLinear_comp, LinearMap.comp_apply, map_sub]
    exact (congrArg _ (sub_eq_zero.2 h₁.symm)).trans (map_zero _)
  rw [hφ, stalkLinear_comp, LinearMap.comp_apply] at h₂
  have h₃ := not_isUnit_of_toSubscheme_eq_zero Y (y := y) (hY.ge rfl) _ h₂
  rw [map_sub, map_sub, stalkLinear_germ, stalkLinear_germ, structureModuleStalkEquiv_germ,
    structureModuleStalkEquiv_germ, ht, map_one] at h₃
  have hu := (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_right h₃
  exact (congrArg IsUnit (X.presheaf.germ_res_apply (homOfLE _) y hc _)).mpr hu

end SerreCriterion


open SerreCriterion in
theorem isAmpleLB_of_subsingleton_coh_one (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X]
    (L : LB X) (hL : L.IsLB)
    (h : ∀ F : X.Modules, IsFiniteQC F →
      ∃ n : ℕ, 1 ≤ n ∧ Subsingleton (coh (twist F (lbPow L n)) 1)) : IsAmpleLB L := by
  refine ⟨hL, inferInstance, fun x => ?_⟩
  obtain ⟨y, hxy, hy⟩ := (isClosed_closure (s := ({x} : Set X))).exists_closed_singleton
    ⟨x, subset_closure rfl⟩
  obtain ⟨W, hW, hyW⟩ := exists_affine_mem y
  let I := Scheme.IdealSheafData.vanishingIdeal W.compl
  have hI : ∀ z, z ∉ I.support ↔ z ∈ W := fun z => by
    rw [← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact not_not
  let Y := Scheme.IdealSheafData.vanishingIdeal (X := X) ⟨{y}, hy⟩
  have hY : (Y.support : Set X) = {y} := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  obtain ⟨n, hn, hz⟩ := h (kernel (idealModuleι I ≫ toSubscheme Y)) (.of_mono (kernel.ι _))
  obtain ⟨t, ht⟩ := exists_idealModuleι_app_eq_one I fun z => (hI z).2
  have hM := isLB_lbPow hL n
  obtain ⟨a, ha⟩ := exists_mem_nonzeroLocus hM _ Y hY hz hyW t ht
  have hle : nonzeroLocus (secOfTwist (idealModuleι I) a) ≤ W := iSup_le fun c z hz => (hI z).1 <| by
    rw [secOfTwist_f] at hz
    exact notMem_support_of_mem_basicOpen I _ ((X.basicOpen_res _ (homOfLE _).op).le hz).2
  refine ⟨n, hn, _, (specializes_iff_mem_closure.2 hxy).mem_open (Opens.isOpen _) ha, ?_⟩
  exact inf_eq_left.2 hle ▸ isAffineOpen_nonzeroLocus_inf hM _ hW

end GlobalTheory
end
end

section

noncomputable section

namespace GlobalTheory.Mem.Col2.IdxEx

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal

variable {X : Fields} {Pr : Primes X} {R : Ranks}


variable (Pr) in
def admitted (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j) : Prop :=
  (P ∈ Pr.vGs → h ∈ stabL X.E _ (lamYat (Pr := Pr) (R := R) j P)) ∧ (P ∉ Pr.vGs → Between j P h)

theorem isAdmissibleIntegralBasisChange_one (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) : admitted Pr j P (1 : AutY X R j) :=
  ⟨fun _ => one_mem _, fun hP => between_of_nf hP (IndefiniteRowSideFullHecke.SandwichNormalForm.nf_one j hP)⟩

def nfMat {E : Type} [Field E] (n c : ℕ) (q : E) (e : Fin c → ℤ) (z : Fin n → E) : Matrix (Fin (n + c)) (Fin (n + c)) E :=
  fun l s => if hs : s.1 < n then (if l = s then 1 else 0)
    else q ^ e ⟨s.1 - n, by omega⟩ * ((if l = s then 1 else 0) + if s.1 = n then Loc.inX E n c z l else 0)

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

abbrev CAt (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) : Subgroup (AutY X R j) :=
  Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) h

def ChiMul (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) : Prop :=
  (∀ r ∈ CAt sel mu cst j P h, chiInv Ch sel mu cst j P h r ≠ 0) ∧
    ∀ r ∈ CAt sel mu cst j P h, ∀ r' ∈ CAt sel mu cst j P h,
      chiInv Ch sel mu cst j P h (r * r') = chiInv Ch sel mu cst j P h r * chiInv Ch sel mu cst j P h r'

def ChiTriv (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) : Prop :=
  ∀ r ∈ CAt sel mu cst j P h, r ∈ Loc.fixX X.E (R.N j) (cOf R j) → chiInv Ch sel mu cst j P h r = 1

def GrpG (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) (lev : Lev (𝓞 X.E ⧸ P.1.asIdeal) X.K (R.N j)) : Prop :=
  ∀ hbar : GL (Fin (R.N j)) (𝓞 X.E ⧸ P.1.asIdeal), hbar ∈ lev.H ↔ ∃ g ∈ prCat (Pr := Pr) cst.sharp j P.1 h,
    ∀ x ∈ stdAt X.E (R.N j) P.1, redV P.1 (g x) = hbar.1.mulVec (redV P.1 x)

def ChrG (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) (lev : Lev (𝓞 X.E ⧸ P.1.asIdeal) X.K (R.N j)) : Prop :=
  ∀ (hbar : ↥lev.H) (g : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) (r : AutY X R j), r ∈ CAt sel mu cst j P h →
    (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (g x)) →
    (∀ x ∈ stdAt X.E (R.N j) P.1, redV P.1 (g x) = hbar.1.1.mulVec (redV P.1 x)) →
    ((lev.lam hbar : X.Kˣ) : X.K) = chiInv Ch sel mu cst j P h r

def GrpQ (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) (lev : LevI X.E X.K (R.N j) P.1) : Prop :=
  lev.H = (prCat (Pr := Pr) cst.sharp j P.1 h).subgroupOf (GLint X.E (R.N j) P.1)

def ChrQ (j : ℕ) (P : rowSG Pr sel mu) (h : AutY X R j) (lev : LevI X.E X.K (R.N j) P.1) : Prop :=
  ∀ (g : ↥lev.H) (r : AutY X R j), r ∈ CAt sel mu cst j P h →
    (∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (g.1.1 x)) →
    ((lev.lam g : X.Kˣ) : X.K) = chiInv Ch sel mu cst j P h r

theorem exists_char {G H K : Type} [Group G] [Group H] [Field K] (C : Subgroup G) (χ : G → K) (Rel : G → H → Prop)
    (hne : ∀ r ∈ C, χ r ≠ 0) (hmul : ∀ r ∈ C, ∀ r' ∈ C, χ (r * r') = χ r * χ r')
    (hs : ∀ h, ∃ r ∈ C, Rel r h) (hm : ∀ r h r' h', Rel r h → Rel r' h' → Rel (r * r') (h * h'))
    (hw : ∀ h, ∀ r ∈ C, ∀ r' ∈ C, Rel r h → Rel r' h → χ r = χ r') :
    ∃ lam : H →* Kˣ, ∀ h, ∀ r ∈ C, Rel r h → ((lam h : Kˣ) : K) = χ r := by
  choose s hsC hsR using hs
  refine ⟨MonoidHom.mk' (fun h => Units.mk0 (χ (s h)) (hne _ (hsC h))) fun a b => Units.ext ?_, fun h r hr hR => ?_⟩
  · simp only [Units.val_mk0, Units.val_mul]
    rw [← hmul _ (hsC a) _ (hsC b)]
    exact hw _ _ (hsC _) _ (mul_mem (hsC a) (hsC b)) (hsR _) (hm _ _ _ _ (hsR a) (hsR b))
  · exact hw _ _ (hsC _) _ hr (hsR _) hR

end GlobalTheory.Mem.Col2.IdxEx

end
end

section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.local_embeddings_tower_compatible : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (_ : IsPlaceOver A v'), IsLocalExt L h → ∀ (ι : Ω →ₐ[K] Kbar v) (ι' : Ω →ₐ[L] Kbar v'), IsLocEmb A v ι → IsLocEmb A v' ι' → ∃ (f : v.adicCompletion K →+* v'.adicCompletion L) (b : Kbar v ≃+* Kbar v'), Continuous f ∧ (∀ x, b (algebraMap _ _ x) = algebraMap _ _ (f x)) ∧ (∀ z, b (ι z) = ι' z) ∧ (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) ∧ (letI := f.toAlgebra; Module.finrank (v.adicCompletion K) (v'.adicCompletion L) = Module.finrank K L ∧ Continuous (Algebra.trace (v.adicCompletion K) (v'.adicCompletion L)) ∧ (∀ z : L, Algebra.trace (v.adicCompletion K) (v'.adicCompletion L) (algebraMap L _ z) = algebraMap K _ (Algebra.trace K L z)) ∧ Continuous (Algebra.norm (v.adicCompletion K) : v'.adicCompletion L → v.adicCompletion K) ∧ ∀ z : L, Algebra.norm (v.adicCompletion K) (algebraMap L (v'.adicCompletion L) z) = algebraMap K _ (Algebra.norm K z)) := by
  first | exact @GlobalTheory.LocalExtCompletion.exists_completion_ext | exact GlobalTheory.LocalExtCompletion.exists_completion_ext | (intros; apply GlobalTheory.LocalExtCompletion.exists_completion_ext <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.continuous_oscillatorGaussianKernel_right : ∀ (P Q : ℕ) (T : Type) [TopologicalSpace T] (Y : Matrix (Ix P Q) (Fin Q) ℂ) (v φ : Ix P Q → ℂ) (Y' : T → Matrix (Ix P Q) (Fin Q) ℂ) (v' φ' : T → Ix P Q → ℂ), Continuous Y' → Continuous v' → Continuous φ' → (∀ t, IsUnit (Yᴴ * Jm P Q * Y' t).det) → Continuous fun t => ker Y v φ (Y' t) (v' t) (φ' t) := by
  first | exact @GlobalTheory.OscGauss.continuous_ker_right | exact GlobalTheory.OscGauss.continuous_ker_right | (intros; apply GlobalTheory.OscGauss.continuous_ker_right <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.gaussian_inner_eq_invariantKernel : ∀ (P Q : ℕ) (Y Y' : Matrix (Ix P Q) (Fin Q) ℂ) (v φ v' φ' : Ix P Q → ℂ), IsUnit Y.toRows₂.det → IsUnit Y'.toRows₂.det → IsUnit (1 - (matA Y)ᴴ * matA Y').det → let A := matA Y; let B := matA Y'; let a : Fin P → ℂ := fun i => star (linX Y v φ (Sum.inl i)); let b : Fin Q → ℂ := fun j => star (linX Y v φ (Sum.inr j)); let c : Fin P → ℂ := fun i => linX Y' v' φ' (Sum.inl i); let d : Fin Q → ℂ := fun j => linX Y' v' φ' (Sum.inr j); let M := (1 - B * Aᴴ)⁻¹; let N := (1 - Aᴴ * B)⁻¹; star (scal Y v φ) * scal Y' v' φ' * (((1 - Aᴴ * B).det)⁻¹ * Complex.exp (a ⬝ᵥ M *ᵥ c + d ⬝ᵥ N *ᵥ b + a ⬝ᵥ (M * B) *ᵥ b + d ⬝ᵥ (N * Aᴴ) *ᵥ c)) = ker Y v φ Y' v' φ' := by
  first | exact @GlobalTheory.OscGauss.kerAlg | exact GlobalTheory.OscGauss.kerAlg | (intros; apply GlobalTheory.OscGauss.kerAlg <;> assumption)
end

section

open MvPolynomial

theorem _root_.GlobalTheory.T.dual_bases_colProd_alt : (∀ (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N) (h : MvPolynomial (Fin N × Fin N) ℚ),
    h ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ N N (fun r => Y.rowLen r) →
    ∑ J : GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N Y, Formalism.GradedWeylDivisibility.fockQ h (GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J
      = Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ le_rfl (fun r : Fin N => Y.rowLen r)) (Formalism.GradedWeylDivisibility.hw ℚ le_rfl (fun r : Fin N => Y.rowLen r)) • h) →
  ∀ (N : ℕ) (Y : YoungDiagram) (hY : Y.colLen 0 ≤ N),
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (b g : ι → MvPolynomial (Fin N × Fin N) ℚ)
    (c : GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N Y → ι → ℤ) (d : ι → GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N Y → ℤ) (Nc : ℚ), Nc ≠ 0 ∧
    (∀ J, GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J = ∑ k, (c J k : ℚ) • b k) ∧
    (∀ k, b k = ∑ J, (d k J : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) ∧
    (∀ k, g k = ∑ J, (c J k : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N Y hY J) ∧
    (∀ i k, Formalism.GradedWeylDivisibility.fockQ (b i) (g k) = if i = k then Nc else 0) ∧
    Submodule.span ℤ (Set.range g) =
      (Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl (fun r : Fin N => Y.rowLen r)).map (Formalism.GradedWeylDivisibility.intQ N N) := by
  first | exact @GlobalTheory.WeylLatDualProof.dual_bases_colProd | exact GlobalTheory.WeylLatDualProof.dual_bases_colProd | (intros; apply GlobalTheory.WeylLatDualProof.dual_bases_colProd <;> assumption)
end
