module

import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle076
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle028
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle078
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle008
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle084
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinrankEqOfInjectiveOfSpan
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianFormsSameSignatureSameSpace
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle015
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle077
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle032
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle083
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralTmulOneMulMemAdelicCompletion
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianLatticeSignatureSplitOfIndefinite
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
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame

@[expose] public section

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member.Arch

theorem unit_iff {E : Type} [CommRing E] {n : Type} [Fintype n] (τ : E →+* ℂ) (G : Matrix n n E) (u : Matrix n n ℂ) :
    uᵀ * (-Gᵀ).map τ * u.map (starRingEnd ℂ) = (-Gᵀ).map τ ↔ uᴴ * G.map τ * u = G.map τ := by
  have e : (-Gᵀ).map τ = -(G.map τ)ᵀ := by
    ext a b; simp
  have e2 : u.map (starRingEnd ℂ) = (uᴴ)ᵀ := by
    ext a b; simp
  rw [e, e2, Matrix.mul_neg, Matrix.neg_mul, neg_inj, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Matrix.transpose_mul]
  exact Matrix.transpose_injective.eq_iff

theorem form_map {A : Type} [CommRing A] {n : Type} [Fintype n] (s : A →+* A) (φ : A →+* ℂ)
    (h : ∀ z, φ (s z) = starRingEnd ℂ (φ z)) (M J : Matrix n n A) :
    (Formalism.UG.cT s M * J * M).map φ = (M.map φ)ᴴ * J.map φ * M.map φ := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 2
  ext a b
  exact h _

theorem mat_ext {A : Type} [CommRing A] {n ι : Type} (θ : ι → (A →+* ℂ))
    (hθ : Function.Injective fun (z : A) (i : ι) => θ i z) {M N : Matrix n n A}
    (h : ∀ i, M.map (θ i) = N.map (θ i)) : M = N :=
  Matrix.ext fun a b => hθ (funext fun i => congrFun (congrFun (h i) a) b)

theorem exists_lift {A : Type} [CommRing A] {n ι : Type} [Fintype n] [DecidableEq n] (s : A →+* A)
    (θ : ι → (A →+* ℂ)) (hθ : Function.Bijective fun (z : A) (i : ι) => θ i z)
    (hs : ∀ i z, θ i (s z) = starRingEnd ℂ (θ i z)) (J : Matrix n n A) (hJ : ∀ i, (J.map (θ i)).det ≠ 0)
    (u : ι → Matrix n n ℂ) (hu : ∀ i, (u i)ᴴ * J.map (θ i) * u i = J.map (θ i)) :
    ∃ g : GL n A, g ∈ Formalism.UG.UJ s J ∧ ∀ i, g.1.map (θ i) = u i := by
  have lift : ∀ w : ι → Matrix n n ℂ, ∃ M : Matrix n n A, ∀ i, M.map (θ i) = w i := by
    intro w
    choose M hM using fun a b => hθ.2 fun i => w i a b
    exact ⟨Matrix.of M, fun i => Matrix.ext fun a b => congrFun (hM a b) i⟩
  have hd : ∀ i, IsUnit (u i).det := by
    intro i
    refine IsUnit.mk0 _ fun h0 => hJ i ?_
    rw [← hu i, Matrix.det_mul, h0, mul_zero]
  obtain ⟨M, hM⟩ := lift u
  obtain ⟨N, hN⟩ := lift fun i => (u i)⁻¹
  refine ⟨⟨M, N, mat_ext θ hθ.1 fun i => ?_, mat_ext θ hθ.1 fun i => ?_⟩, mat_ext θ hθ.1 fun i => ?_, hM⟩
  · rw [Matrix.map_mul, hM, hN, Matrix.mul_nonsing_inv _ (hd i), Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [Matrix.map_mul, hM, hN, Matrix.nonsing_inv_mul _ (hd i), Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [form_map s (θ i) (hs i), hM, hu]

theorem gram_det_ne_zero {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) :
    S.gram.det ≠ 0 := by
  apply GlobalTheory.RecDict.det_gram_ne_zero <;> assumption

theorem continuous_inf (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] :
    Continuous (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) : AF F ⊗[F] E → Ainf F ⊗[F] E) := by
  have : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (Ainf F ⊗[F] E) := IsModuleTopology.toContinuousAdd (Ainf F) _
  have : ContinuousSMul (Ainf F) (Ainf F ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
  let φ : AF F ⊗[F] E →ₛₗ[(fstA F).toRingHom] Ainf F ⊗[F] E :=
    { toFun := Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)
      map_add' := map_add _
      map_smul' := fun a x => by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        rfl }
  have hs : Continuous ((fstA F).toRingHom : AF F → Ainf F) := continuous_fst
  exact IsModuleTopology.continuous_of_linearMapₛₗ hs φ

theorem inf_mem {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (g : GL (Fin n) (AF F ⊗[F] E)) (hg : g ∈ HR (AF F) σ J) :
    Formalism.UG.bc (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom g ∈ HR (Ainf F) σ J := by
  let π : AF F ⊗[F] E →+* Ainf F ⊗[F] E := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
  have hπ : ∀ z, π (sigR (AF F) σ z) = sigR (Ainf F) σ (π z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]
    | tmul a x => rfl
  have hg' : Formalism.UG.cT (sigR (AF F) σ) g.1 * JR (AF F) J * g.1 = JR (AF F) J := hg
  have hJ : (JR (F := F) (AF F) J).map π = JR (Ainf F) J := rfl
  have hc : (Formalism.UG.cT (sigR (AF F) σ) g.1).map π = Formalism.UG.cT (sigR (Ainf F) σ) (g.1.map π) :=
    Matrix.ext fun a b => hπ _
  change Formalism.UG.cT (sigR (Ainf F) σ) (g.1.map π) * JR (Ainf F) J * g.1.map π = JR (Ainf F) J
  rw [← hc, ← hJ, ← Matrix.map_mul, ← Matrix.map_mul, hg']

variable {D : D7}

theorem JR_map (V : HSp D) {τ : D.host.E →+* ℂ} {θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ}
    (h : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) : (JR (F := D.host.F) (Ainf D.host.F) V.gram).map θ = V.gram.map τ :=
  Matrix.ext fun _ _ => h.1 _

theorem archM_of_one (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) {k : GA D V}
    (hk : infHom V k = 1) : archM V θ k = 1 := by
  rw [archM, hk, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem continuous_archM (V : HSp D) {θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ} (hθ : Continuous θ) :
    Continuous fun h => archM V θ h := by
  have h1 : Continuous fun h : GA D V => (matHom V h).1 :=
    Units.continuous_val.comp (continuous_subtype_val (p := (· ∈ HR (AF D.host.F) D.sp.cm.sig V.gram)))
  exact (h1.matrix_map (continuous_inf D.host.F D.host.E)).matrix_map hθ

theorem archM_spec : ∀ (D : D7) (V : HSp D), ∀ (θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (θ τ)) → (∀ τ, archM V (θ τ) 1 = 1 ∧ (∀ h h', archM V (θ τ) (h * h') = archM V (θ τ) h * archM V (θ τ) h') ∧ (∀ k ∈ GfC V, archM V (θ τ) k = 1) ∧ Continuous (fun h => archM V (θ τ) h) ∧ ∀ h, (archM V (θ τ) h)ᵀ * (-V.gramᵀ).map τ * (archM V (θ τ) h).map (starRingEnd ℂ) = (-V.gramᵀ).map τ) ∧ (∀ h, (∀ τ, τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD → archM V (θ τ) h = 1) → h ∈ GfC V) ∧ ∀ u : (D.host.E →+* ℂ) → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD → (u τ)ᵀ * (-V.gramᵀ).map τ * (u τ).map (starRingEnd ℂ) = (-V.gramᵀ).map τ) → ∃ a ∈ GinfC V, ∀ τ, τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD → archM V (θ τ) a = u τ := by
  intro D V θ hθ
  obtain ⟨hc, hs, hb⟩ := (GlobalTheory.T.realAdeles_cmField_equiv_complex_cmType D).2 θ hθ
  refine ⟨fun τ => ⟨archM_of_one V _ (map_one _), fun h h' => ?_, fun k hk => archM_of_one V _ hk,
    continuous_archM V (hc τ), fun h => ?_⟩, fun h hh => ?_, fun u hu => ?_⟩
  · rw [archM, archM, archM, map_mul, Units.val_mul, Matrix.map_mul]
  · have hm : Formalism.UG.cT (sigR (Ainf D.host.F) D.sp.cm.sig) (infHom V h).1 * JR (Ainf D.host.F) V.gram * (infHom V h).1 =
        JR (Ainf D.host.F) V.gram := inf_mem D.sp.cm.sig V.gram (matHom V h) h.2
    rw [unit_iff, ← JR_map V (hθ τ), archM, ← form_map _ _ (hs τ), hm]
  · refine Units.ext (mat_ext _ hb.1 fun τ => ?_)
    rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hh τ.1 τ.2
  · obtain ⟨g, hg, hgu⟩ := exists_lift (sigR (Ainf D.host.F) D.sp.cm.sig) _ hb (fun τ => hs τ.1)
      (JR (Ainf D.host.F) V.gram) (fun τ => by
        rw [JR_map V (hθ τ.1)]
        have : (V.gram.map τ.1).det = τ.1 V.gram.det := (τ.1.map_det V.gram).symm
        rw [this]
        exact (map_ne_zero τ.1).2 (gram_det_ne_zero V)) (fun τ => u τ.1) (fun τ => by
        rw [JR_map V (hθ τ.1)]
        exact (unit_iff _ _ _).1 (hu τ.1 τ.2))
    obtain ⟨a, ha, hag⟩ := (GlobalTheory.T.adelicUnitary_eq_real_mul_finite_split D V).2.2.2.2 g hg
    refine ⟨a, ha, fun τ hτ => ?_⟩
    rw [archM, hag]
    exact hgu ⟨τ, hτ⟩

end GlobalTheory.Member.Arch
end

section

noncomputable section

namespace GlobalTheory.Member.PrincLevel

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem smul_mem_hat (L : Set (Fin n → E)) (a : FiniteAdeleRing (𝓞 F) F)
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) {z : Fin n → GlobalTheory.AdLat.RA F E}
    (hz : z ∈ GlobalTheory.AdLat.hat F L) : a • z ∈ GlobalTheory.AdLat.hat F L := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a * b, fun v => ?_, x, hx, ?_⟩
    · exact mul_mem (ha v) (hb v)
    · funext i
      simp only [Pi.smul_apply, TensorProduct.smul_tmul', smul_eq_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

def congSub {R : Type} [CommRing R] (M : Matrix (Fin n) (Fin n) R) (H : AddSubgroup (Fin n → R)) (N : ℕ) :
    AddSubgroup (Fin n → R) where
  carrier := {z | ∃ y ∈ H, M *ᵥ z - z = N • y}
  zero_mem' := ⟨0, zero_mem _, by simp⟩
  add_mem' := by
    rintro a b ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
    refine ⟨x + y, add_mem hx hy, ?_⟩
    rw [Matrix.mulVec_add, smul_add, ← ha, ← hb]; abel
  neg_mem' := by
    rintro a ⟨x, hx, ha⟩
    refine ⟨-x, neg_mem hx, ?_⟩
    rw [Matrix.mulVec_neg, smul_neg, ← ha]; abel

theorem cong_of_gen (L : Set (Fin n → E)) (S : Set (Fin n → E)) (hS : L ⊆ AddSubgroup.closure S)
    (M : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) (N : ℕ)
    (h : ∀ x ∈ S, ∃ y ∈ GlobalTheory.AdLat.hat F L, M *ᵥ GlobalTheory.AdLat.fv F x - GlobalTheory.AdLat.fv F x = N • y) :
    ∀ z ∈ GlobalTheory.AdLat.hat F L, ∃ y ∈ GlobalTheory.AdLat.hat F L, M *ᵥ z - z = N • y := by
  have h1 : ∀ x ∈ AddSubgroup.closure S, GlobalTheory.AdLat.fv F x ∈ congSub M (GlobalTheory.AdLat.hat F L) N := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem z hz => exact h z hz
    | zero =>
      have : GlobalTheory.AdLat.fv F (0 : Fin n → E) = 0 := by funext i; simp [GlobalTheory.AdLat.fv]
      rw [this]; exact zero_mem _
    | add x y _ _ hx hy =>
      have : GlobalTheory.AdLat.fv F (x + y) = GlobalTheory.AdLat.fv F x + GlobalTheory.AdLat.fv F y := by
        funext i; simp [GlobalTheory.AdLat.fv, TensorProduct.tmul_add]
      rw [this]; exact add_mem hx hy
    | neg x _ hx =>
      have : GlobalTheory.AdLat.fv F (-x) = -GlobalTheory.AdLat.fv F x := by
        funext i; simp [GlobalTheory.AdLat.fv, TensorProduct.tmul_neg]
      rw [this]; exact neg_mem hx
  have h2 : GlobalTheory.AdLat.hat F L ≤ congSub M (GlobalTheory.AdLat.hat F L) N := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, x, hx, rfl⟩
    obtain ⟨y, hy, e⟩ := h1 x (hS hx)
    have hz : (fun i => a ⊗ₜ[F] x i : Fin n → GlobalTheory.AdLat.RA F E) = a • GlobalTheory.AdLat.fv F x := by
      funext i
      simp only [GlobalTheory.AdLat.fv, Pi.smul_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    refine ⟨a • y, smul_mem_hat L a ha hy, ?_⟩
    rw [hz, Matrix.mulVec_smul, ← smul_sub, e, smul_comm]
  exact fun z hz => h2 hz

theorem continuous_mulVec_sub {X R : Type} [TopologicalSpace X] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] {f : X → Matrix (Fin n) (Fin n) R} (hf : Continuous f) (v : Fin n → R) :
    Continuous fun k => f k *ᵥ v - v :=
  (hf.matrix_mulVec continuous_const).sub continuous_const

end General

variable {D : D7}

theorem finCong_map {V : HSp D} {N : ℕ} {k : GA D V} (hk : FinCong V N k) :
    ∀ z ∈ latHat V, (finHom V k).1 *ᵥ z ∈ latHat V := by
  intro z hz
  obtain ⟨y, hy, e⟩ := hk z hz
  rw [sub_eq_iff_eq_add] at e
  rw [e]
  exact add_mem (nsmul_mem hy N) hz

theorem finCong_one (V : HSp D) (N : ℕ) : FinCong V N 1 := by
  intro z _
  exact ⟨0, zero_mem _, by simp⟩

theorem finCong_mul {V : HSp D} {N : ℕ} {a b : GA D V} (ha : FinCong V N a) (hb : FinCong V N b) :
    FinCong V N (a * b) := by
  intro z hz
  obtain ⟨y, hy, e⟩ := hb z hz
  obtain ⟨x, hx, e'⟩ := ha _ (finCong_map hb z hz)
  refine ⟨x + y, add_mem hx hy, ?_⟩
  rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, nsmul_add, ← e, ← e']
  abel

theorem finCong_inv {V : HSp D} {N : ℕ} {a : GA D V} (ha : FinCong V N a) : FinCong V N a⁻¹ := by
  obtain ⟨h1, -, h3, h4, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have hinv : ∀ z ∈ latHat V, (finHom V a⁻¹).1 *ᵥ z ∈ latHat V := by
    have hm := finCong_map ha
    rw [h1] at hm ⊢
    rw [map_inv]
    exact GlobalTheory.AdLat.inv_mulVec_mem_hat D.host.F D.host.E V.rank (latC V) (finHom V a) (cF D) h3 h4 hm
      (GlobalTheory.Member.finHom_herm_det D V a).2.1
  intro z hz
  obtain ⟨y, hy, e⟩ := ha _ (hinv z hz)
  refine ⟨-y, neg_mem hy, ?_⟩
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
    Matrix.one_mulVec] at e
  rw [neg_nsmul, ← e, neg_sub]

def levelGroup (V : HSp D) (N : ℕ) : Subgroup (GA D V) where
  carrier := {k | k ∈ GfC V ∧ FinCong V N k}
  one_mem' := ⟨one_mem _, finCong_one V N⟩
  mul_mem' := fun ha hb => ⟨mul_mem ha.1 hb.1, finCong_mul ha.2 hb.2⟩
  inv_mem' := fun ha => ⟨inv_mem ha.1, finCong_inv ha.2⟩

theorem finCong_mem_nhds (V : HSp D) {N : ℕ} (hN : 0 < N) :
    {k : GA D V | FinCong V N k} ∈ 𝓝 (1 : GA D V) := by
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨hop, hc, -⟩ := GlobalTheory.Member.latHat_open_and_continuous D V
  have : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (Af D.host.F) _
  obtain ⟨S, hS⟩ := h3.restrictScalars (R := ℤ)
  have hLS : (latC V : Set (Fin V.rank → D.host.E)) ⊆
      (AddSubgroup.closure (S : Set (Fin V.rank → D.host.E)) : AddSubgroup (Fin V.rank → D.host.E)) := by
    intro x hx
    have hx' : x ∈ Submodule.span ℤ (S : Set (Fin V.rank → D.host.E)) := by rw [hS]; exact hx
    rw [← Submodule.span_int_eq_addSubgroupClosure]
    exact hx'
  have hU : (⋂ x ∈ S, {k : GA D V | ∃ y ∈ latHat V,
      (finHom V k).1 *ᵥ GlobalTheory.AdLat.fv D.host.F x - GlobalTheory.AdLat.fv D.host.F x = N • y}) ∈ 𝓝 (1 : GA D V) := by
    refine (Filter.biInter_finset_mem S).2 fun x _ => ?_
    have hcx : Continuous fun k : GA D V =>
        (finHom V k).1 *ᵥ GlobalTheory.AdLat.fv D.host.F x - GlobalTheory.AdLat.fv D.host.F x :=
      continuous_mulVec_sub hc _
    refine ((hop N hN).preimage hcx).mem_nhds ⟨0, zero_mem _, by simp⟩
  refine Filter.mem_of_superset hU fun k hk => ?_
  simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hk
  unfold FinCong
  rw [Set.mem_ofPred_eq]
  rw [h1] at hk ⊢
  exact cong_of_gen _ _ hLS _ N fun x hx => hk x hx

theorem exists_levelK_and_nhds : ∀ (D : D7) (V : HSp D), ∀ N : ℕ,
    (∃ Kf : Subgroup (GA D V), IsLevelK V N Kf) ∧
      (0 < N → {k : GA D V | FinCong V N k} ∈ 𝓝 (1 : GA D V)) :=
  fun _ V N => ⟨⟨levelGroup V N, fun _ => Iff.rfl⟩, fun hN => finCong_mem_nhds V hN⟩

end GlobalTheory.Member.PrincLevel
end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

theorem _root_.GlobalTheory.T.adelicElementLattice_full_and_completion : ∀ (D : D7) (V : HSp D), ∀ g : GA D V, (latG V g).FG ∧ Submodule.span D.host.E (latG V g : Set (Fin V.rank → D.host.E)) = ⊤ ∧ (latG V g : Set (Fin V.rank → D.host.E)) = GlobalTheory.AdLat.latOf D.host.F (finHom V g).1 (latG V 1 : Set (Fin V.rank → D.host.E)) ∧ (latGHat V g : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)) = (finHom V g).1.mulVec '' (GlobalTheory.AdLat.hat D.host.F (latG V 1 : Set (Fin V.rank → D.host.E))) ∧ latGHat V g = GlobalTheory.AdLat.hat D.host.F (latG V g : Set (Fin V.rank → D.host.E)) ∧ latG V 1 = Submodule.span (𝓞 D.host.E) {w | ∃ a ∈ D.host.AA, ∃ x ∈ latC V, w = a • x} := by
  first | exact @GlobalTheory.Member.latG_lattice_and_completion | exact GlobalTheory.Member.latG_lattice_and_completion | (intros; apply GlobalTheory.Member.latG_lattice_and_completion <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem halfVec_mem_latHat {D : D7} (V : HSp D) (b : 𝓞 D.host.E)
    (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) (hz : z ∈ latHat V) :
    halfVec V b z ∈ latHat V := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨a, ha, b • x, V.L0.smul_mem b hx, ?_⟩
    funext i
    have e : b • x = (b : D.host.E) • x := (algebraMap_smul D.host.E b x).symm
    simp only [halfVec, Algebra.TensorProduct.tmul_mul_tmul, one_mul, e, map_smul,
      Finsupp.smul_apply, smul_eq_mul]
  | zero =>
    have : halfVec V b 0 = 0 := by funext i; simp [halfVec]
    rw [this]; exact zero_mem _
  | add w w' _ _ h h' =>
    have : halfVec V b (w + w') = halfVec V b w + halfVec V b w' := by
      funext i; simp only [halfVec, Pi.add_apply, mul_add]
    rw [this]; exact add_mem h h'
  | neg w _ h =>
    have : halfVec V b (-w) = - halfVec V b w := by
      funext i; simp only [halfVec, Pi.neg_apply, mul_neg]
    rw [this]; exact neg_mem h

theorem finCong_iff_half (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H) (V : HSp D)
    (k : GA D V) :
    FinCong V l.M k ↔ ∀ b ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E), ∀ z ∈ latHat V,
      ∃ y ∈ latHat V, (finHom V k).1.mulVec (halfVec V b z) - halfVec V b z = l.M • y := by
  refine ⟨fun h b _ z hz => h _ (halfVec_mem_latHat V b z hz), fun h => ?_⟩
  obtain ⟨h1, -, h3, h4, h5, h6, -, h8, h9, -, h11⟩ := latHat_eq_hat_and_gram D V
  unfold FinCong
  rw [h1] at h ⊢
  refine GlobalTheory.AdLat.trivial_level_of_half D.host.F D.host.E V.rank (latC V) (cF D) V.gramᵀ 1
    (finHom V k) l.M (l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) l.Mb h3 h4 h5 h8 h9
    one_ne_zero h11 (GlobalTheory.T.finitePart_preserves_form_det_norm_one D V k).1 (lt_of_lt_of_le (by norm_num) l.three_le)
    (by rw [sup_comm]; exact l.coprime) (by rw [mul_comm]; exact l.prod) ?_ h
  intro b hb
  refine ⟨H.bar b, Ideal.mem_map_of_mem _ hb, ?_⟩
  rw [h6]
  exact H.bar_eq b

theorem finCong_iff_half_and_kfHalf : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H) (V : HSp D), (∀ k : GA D V, FinCong V l.M k ↔ ∀ b ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E), ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec (halfVec V b z) - halfVec V b z = l.M • y) ∧ ∀ Kf : Subgroup (GA D V), IsLevelK V l.M Kf → KfHalf V Kf l.M (l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) := by
  intro D H l V
  refine ⟨finCong_iff_half D H l V, fun Kf hK k => ?_⟩
  rw [hK k]
  exact and_congr_right fun _ => finCong_iff_half D H l V k

end GlobalTheory.Member
end

section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem exists_den_herm_model (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E)
    (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (hξ : cc ξ = -ξ)
    (h : Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧
      (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧
      ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ x) (φ y))) :
    ∃ den : 𝓞 E, den ≠ 0 ∧ ∀ x ∈ LinearMap.range φ, ∀ y ∈ LinearMap.range φ,
      IsIntegral ℤ ((den : E) * herm Gm x y) := by
  by_cases hξ0 : ξ = 0
  · have hz : ∀ z : D.La, z = 0 := fun z => by
      apply D.unimod.1
      ext y
      have := h.2.2.2.2 z y
      rw [hξ0, zero_mul, map_zero] at this
      simpa using this
    refine ⟨1, one_ne_zero, ?_⟩
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [hz y, map_zero, GlobalTheory.HermModel.herm_zero_right, mul_zero]
    exact isIntegral_zero
  · have hint := (GlobalTheory.HermModel.rank_integral_selfDual E H D r ξ Gm φ hξ h).2.2.1
    have halg : IsAlgebraic ℤ ξ :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic ξ)
    obtain ⟨n, hn0, hn⟩ := halg.exists_integral_multiple
    have hd : IsIntegral ℤ ((NumberField.discr E : E) * (n • ξ)) :=
      (isIntegral_algebraMap (R := ℤ) (A := E) (x := NumberField.discr E)).mul hn
    refine ⟨⟨_, hd⟩, ?_, ?_⟩
    · intro h0
      have h1 : (NumberField.discr E : E) * (n • ξ) = 0 := congrArg Subtype.val h0
      rw [zsmul_eq_mul] at h1
      exact mul_ne_zero (Int.cast_ne_zero.2 (NumberField.discr_ne_zero E))
        (mul_ne_zero (Int.cast_ne_zero.2 hn0) hξ0) h1
    · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      have h2 := (isIntegral_algebraMap (R := ℤ) (A := E) (x := n)).mul (hint x y)
      have e : (NumberField.discr E : E) * (n • ξ) * herm Gm (φ x) (φ y) =
          algebraMap ℤ E n * ((NumberField.discr E : E) * (ξ * herm Gm (φ x) (φ y))) := by
        rw [zsmul_eq_mul, eq_intCast]; ring
      change IsIntegral ℤ ((NumberField.discr E : E) * (n • ξ) * herm Gm (φ x) (φ y))
      rw [e]; exact h2

theorem latModel_of_same_signature : GlobalTheory.Published.HasseNormSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (Dw Di : Datum H) (r : ℕ) (Ψ : Finset (E →+* ℂ)) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)), Di.p = Dw.p → Di.q = Dw.q → (∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) → cc ξ₀ = -ξ₀ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ x) (φ y))) → LatModel l Ψ Gm ξ₀ Dw.q Di := by
  intro hN E _ _ _ H l Dw Di r Ψ ξ₀ Gm φ hp hq hΨ hξ h
  have hξ' : cc (-ξ₀) = -(-ξ₀) := by
    have : cc (-ξ₀) = -cc ξ₀ := by simp [cc]
    rw [this, hξ]
  obtain ⟨φ0, h0⟩ := GlobalTheory.model_in_same_space (GlobalTheory.LocalQuad.landherrSt_of_hasseNormSt hN) hN
    E H Dw Di r (-ξ₀) Gm φ hp hq hξ' h
  refine ⟨φ0, h0.1, h0.2.2.2.2, ?_, exists_den_herm_model E H Di r (-ξ₀) Gm φ0 hξ' h0,
    GlobalTheory.T.principalLevelGroup_finiteIndex_unitaryStabiliser E H l Di r ξ₀ Gm φ0 hξ h0, GlobalTheory.T.principalGroup_acts_freely_on_flags E H l Di r ξ₀ Gm φ0 hξ h0 Ψ Dw.q hΨ,
    GlobalTheory.T.transvection_mem_principalCongruenceGroup E H l Di r ξ₀ Gm φ0 hξ h0⟩
  rw [LinearMap.coe_range]; exact h0.2.1

end GlobalTheory.FrameUnif
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.hermitianLatticeSignatureSplit_of_indefinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0) → 3 ≤ D.p + D.q → 1 ≤ D.p → 1 ≤ D.q → SplitLat D := by
  first | exact @GlobalTheory.SplitGenus.splitLat_of_indefinite | exact GlobalTheory.SplitGenus.splitLat_of_indefinite | (intros; apply GlobalTheory.SplitGenus.splitLat_of_indefinite <;> assumption)
end
