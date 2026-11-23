module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197

@[expose] public section

section

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThK.RealUniq

open GlobalTheory.RealActs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isHecke_div' {χ χ' : Chr F E} (h : GlobalTheory.LFun.IsHecke F E χ) (h' : GlobalTheory.LFun.IsHecke F E χ') :
    GlobalTheory.LFun.IsHecke F E (χ / χ') :=
  ⟨h.1.div' h'.1, fun x => by simp only [MonoidHom.div_apply, h.2 x, h'.2 x, div_self']⟩

theorem resEtaPow_div' {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {K : Subgroup Rˣ}
    {χ χ' : Aˣ →* Circle} {n m k : ℕ} (h : ResEtaPow K χ n) (h' : ResEtaPow K χ' m) (hk : k = n + m) :
    ResEtaPow K (χ / χ') k := by
  subst hk
  intro a
  have e := h a
  have e' := h' a
  rw [MonoidHom.div_apply, Circle.coe_div, e, e']
  split_ifs
  · simp
  · rw [pow_add]
    rcases neg_one_pow_eq_or ℂ m with hm | hm <;> rw [hm] <;> ring

variable {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem isPair_V (h : IsTriple B G X om om') :
    IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, h.chars.heckeβ, isHecke_div' h.chars.heckeβ h.chars.heckeα, h.chars.resβ,
    resEtaPow_div' h.chars.resβ h.chars.resα rfl, h.weil⟩

theorem isPair_V' (h : IsTriple B G X om om') :
    IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, isHecke_div' h.chars.heckeα h.chars.heckeβ, h.chars.resα,
    resEtaPow_div' h.chars.resα h.chars.resβ (add_comm _ _), h.weil'⟩

theorem det_ne_zero_of_sig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨rfl, A, hA⟩ := h
  let A' : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := A.submatrix id finSumFinEquiv.symm
  have e : A'ᵀ * M * A'.map star =
      (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) _ ℂ).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hA]; rfl
  intro h0
  have e2 := congrArg Matrix.det e
  rw [Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_neg] at e2
  simp at e2
  exact absurd e2.symm (by simp)

variable {κ : Type} [Fintype κ]

theorem actsD_zero (T : ℝ → Module.End ℂ ((κ → AF F) → ℂ)) :
    ActsD (evI F) (fun t => ⇑(T t)) ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _ x
  have e : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by funext y; simp [tens]
  rw [e]
  simp only [map_zero, Pi.zero_apply]
  exact hasDerivAt_const _ _

theorem acts_zero (T : Module.End ℂ ((κ → AF F) → ℂ)) :
    Acts (evI F) ⇑T ⇑(0 : SInf F κ) ⇑(0 : SInf F κ) := by
  intro r _
  have e : tens (evI F) (⇑(0 : SInf F κ)) r = 0 := by funext y; simp [tens]
  rw [e, map_zero]

def induced {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] (π : U →ₗ[ℂ] V)
    (hπ : Function.Surjective π) (D : U →ₗ[ℂ] U) (hD : ∀ u, π u = 0 → π (D u) = 0) : V →ₗ[ℂ] V :=
  (π.quotKerEquivOfSurjective hπ).toLinearMap ∘ₗ (LinearMap.ker π).mapQ (LinearMap.ker π) D (fun u hu => hD u hu) ∘ₗ
    (π.quotKerEquivOfSurjective hπ).symm.toLinearMap

theorem induced_apply {U V : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V] (π : U →ₗ[ℂ] V)
    (hπ : Function.Surjective π) (D : U →ₗ[ℂ] U) (hD : ∀ u, π u = 0 → π (D u) = 0) (u : U) :
    induced π hπ D hD (π u) = π (D u) := by
  have e : (π.quotKerEquivOfSurjective hπ).symm (π u) = Submodule.Quotient.mk u := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [induced, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, e, Submodule.mapQ_apply]
  rfl

end GlobalTheory.ThK.RealUniq

end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.QDom

open scoped Pointwise

theorem isFundamentalDomain_inf {G : Type} [Group G] [MeasurableSpace G] {μ : Measure G}
    (hm : ∀ g : G, Measurable (g * ·)) (hinv : ∀ g : G, μ.map (g * ·) = μ)
    {Γ : Subgroup G} [Countable Γ] {D : Set G} (hD : IsFundamentalDomain Γ D μ) (S : Subgroup G) :
    ∃ 𝓓 : Set G, IsFundamentalDomain ↥(Γ ⊓ S) 𝓓 μ := by
  classical
  let Q' : Subgroup Γ := (Γ ⊓ S).subgroupOf Γ
  haveI : Countable (Γ ⧸ Q') := Function.Surjective.countable QuotientGroup.mk_surjective
  let rep : Γ ⧸ Q' → Γ := fun c => (Quotient.out c)⁻¹
  have hmp : ∀ g : G, MeasurePreserving (g * ·) μ μ := fun g => ⟨hm g, hinv g⟩
  have himg : ∀ (g : G) (s : Set G), g • s = (g⁻¹ * ·) ⁻¹' s := by
    intro g s; ext x; simp [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
  have hnm : ∀ g : G, NullMeasurableSet (g • D) μ := fun g => by
    rw [himg]; exact hD.nullMeasurableSet.preimage (hmp g⁻¹).quasiMeasurePreserving
  refine ⟨⋃ c, ((rep c : Γ) : G) • D, ?_⟩
  refine IsFundamentalDomain.mk'' ?_ ?_ ?_ ?_
  · exact NullMeasurableSet.iUnion fun c => hnm _
  · filter_upwards [hD.ae_covers] with x hx
    obtain ⟨γ, hγ⟩ := hx
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul Q' γ
    have hQ : ((h : Γ) : G) ∈ Γ ⊓ S := (Subgroup.mem_subgroupOf).1 h.2
    refine ⟨⟨((h : Γ) : G)⁻¹, inv_mem hQ⟩, Set.mem_iUnion.2 ⟨(γ : Γ ⧸ Q'), ?_⟩⟩
    rw [himg, Set.mem_preimage]
    have e1 : ((rep (γ : Γ ⧸ Q') : Γ) : G)⁻¹ = (γ : G) * ((h : Γ) : G) := by
      simp only [rep, inv_inv]
      have := congrArg (fun y : Γ => (y : G)) hh
      simpa using this
    rw [e1]
    have : (γ : G) * ((h : Γ) : G) * ((⟨((h : Γ) : G)⁻¹, inv_mem hQ⟩ : ↥(Γ ⊓ S)) • x) = γ • x := by
      rw [Subgroup.smul_def, Subgroup.smul_def]
      simp [smul_eq_mul, mul_assoc]
    rw [this]; exact hγ
  · intro g hg
    have hsm : g • ⋃ c, ((rep c : Γ) : G) • D = ⋃ c, ((g : G) * ((rep c : Γ) : G)) • D := by
      rw [Set.smul_set_iUnion]
      refine Set.iUnion_congr fun c => ?_
      rw [← smul_smul]; rfl
    rw [hsm, AEDisjoint.iUnion_left_iff]
    intro c
    rw [AEDisjoint.iUnion_right_iff]
    intro c'
    have hgΓ : (g : G) ∈ Γ := (Subgroup.mem_inf.1 g.2).1
    let γ₁ : Γ := ⟨g, hgΓ⟩ * rep c
    have hne : γ₁ ≠ rep c' := by
      intro heq
      have hmem : (Quotient.out c)⁻¹ * Quotient.out c' ∈ Q' := by
        rw [Subgroup.mem_subgroupOf]
        have : (Quotient.out c')⁻¹ = ⟨g, hgΓ⟩ * (Quotient.out c)⁻¹ := by
          simpa [γ₁, rep] using heq.symm
        have h2 : (Quotient.out c)⁻¹ * Quotient.out c' = (⟨g, hgΓ⟩ : Γ)⁻¹ := by
          rw [← inv_inj, mul_inv_rev, inv_inv, this, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
        rw [h2]
        simpa using inv_mem g.2
      have hcc : c = c' := by
        rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
        exact (QuotientGroup.eq).2 hmem
      subst hcc
      apply hg
      have : (⟨g, hgΓ⟩ : Γ) = 1 := by simpa [γ₁] using heq
      ext; simpa using congrArg Subtype.val this
    exact hD.aedisjoint hne
  · intro g
    exact (hmp (g : G)).quasiMeasurePreserving

end GlobalTheory.QDom

namespace GlobalTheory.QDom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem countable_numberField : Countable E :=
  Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm

theorem countable_ratU (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Countable (ratU σ J) := by
  classical
  haveI := countable_numberField (E := E)
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  have hmat : Countable (GL (Fin n) E) := Function.Injective.countable (f := fun A : GL (Fin n) E => (A : Matrix (Fin n) (Fin n) E)) Units.val_injective
  have hpre : ∀ x : ratU σ J, ∃ A : GL (Fin n) E, Matrix.GeneralLinearGroup.map (inclR (AF F)) A = ((x : UA σ J) : GL (Fin n) (AE F E)) := by
    intro x
    have := x.2
    unfold ratU at this
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range] at this
    exact this
  choose f hf using hpre
  refine Function.Injective.countable (f := f) ?_
  intro x y hxy
  apply Subtype.ext; apply Subtype.ext
  rw [← hf x, ← hf y, hxy]


theorem measurable_mul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : UA σ J) :
    Measurable (g * ·) := by
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  apply Continuous.measurable
  apply Continuous.subtype_mk
  rw [Units.continuous_iff]
  constructor
  · simp only [Function.comp_def, Subgroup.coe_mul, Units.val_mul]
    exact continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)
  · simp only [Subgroup.coe_mul, mul_inv_rev, Units.val_mul]
    exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_mul continuous_const

end GlobalTheory.QDom

namespace GlobalTheory.QDom

theorem exists_fundamentalDomain_ratStab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∃ 𝓓 : Set (UA σ G.V.J), IsFundamentalDomain ↥(ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H.x = incV F H.x}) 𝓓 G.M.μ := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' _ X om om' hT
  haveI := countable_ratU σ G.V.J
  have hgood := hT.geo.hM
  haveI := hgood.haar
  exact isFundamentalDomain_inf (measurable_mul_left σ G.V.J) (fun g => map_mul_left_eq_self G.M.μ g) hgood.dom _

end GlobalTheory.QDom
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixedLagr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def hat {κ : Type} (w : (κ → F) × (κ → F)) : (κ → AF F) × (κ → AF F) :=
  (fun i => algebraMap F (AF F) (w.1 i), fun i => algebraMap F (AF F) (w.2 i))

theorem hat_add {κ : Type} (a b : (κ → F) × (κ → F)) : hat (a + b) = hat a + hat b := by
  simp only [hat, Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add (f := _)]; rfl

theorem hat_smul {κ : Type} (c : F) (a : (κ → F) × (κ → F)) : hat (c • a) = algebraMap F (AF F) c • hat a := by
  simp only [hat, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul]; rfl

theorem hat_zero {κ : Type} : hat (0 : (κ → F) × (κ → F)) = 0 := by
  simp only [hat, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, map_zero]; rfl

theorem schr_comp {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, Prod.fst_add, Prod.snd_add,
    add_assoc, add_dotProduct, dotProduct_add]
  congr 2
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * invOf_mul_self (2 : R)

variable {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

def IsMixed (M₁ : Model σ X W₁) (H' : Plane E d d₁) (m : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Prop :=
  ∃ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))), ∃ z : Matrix (Fin n) (Fin d₁) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    (M₁.co.e z).1 = 0 ∧ m = u + incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ

theorem isMixed_zero (M₁ : Model σ X W₁) (H' : Plane E d d₁) : IsMixed M₁ H' 0 :=
  ⟨0, ⟨0, by ext i j; simp [Matrix.vecMulVec_apply]⟩, 0, by simp, by simp⟩

theorem IsMixed.add {M₁ : Model σ X W₁} {H' : Plane E d d₁} {m m' : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))}
    (h : IsMixed M₁ H' m) (h' : IsMixed M₁ H' m') : IsMixed M₁ H' (m + m') := by
  obtain ⟨u, ⟨y, rfl⟩, z, hz, rfl⟩ := h
  obtain ⟨u', ⟨y', rfl⟩, z', hz', rfl⟩ := h'
  refine ⟨Matrix.vecMulVec (y + y') (incV F H'.x), ⟨y + y', rfl⟩, z + z', by simp [hz, hz'], ?_⟩
  rw [Matrix.add_vecMulVec, Matrix.mul_add, Matrix.add_mul]
  abel

theorem IsMixed.smul {M₁ : Model σ X W₁} {H' : Plane E d d₁} {m : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))}
    (h : IsMixed M₁ H' m) (t : AF F) : IsMixed M₁ H' (t • m) := by
  obtain ⟨u, ⟨y, rfl⟩, z, hz, rfl⟩ := h
  refine ⟨Matrix.vecMulVec (t • y) (incV F H'.x), ⟨t • y, rfl⟩, t • z, by simp [hz], ?_⟩
  rw [smul_add, Matrix.smul_vecMulVec, Matrix.mul_smul, Matrix.smul_mul]

def lagr (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) :
    Submodule F ((Fin n × Fin d → F) × (Fin n × Fin d → F)) where
  carrier := {w | IsMixed M₁ H' (M.co.e.symm (hat w))}
  zero_mem' := by simpa [hat_zero] using isMixed_zero M₁ H'
  add_mem' := fun ha hb => by simpa [Set.mem_setOf_eq, hat_add, map_add (f := _)] using ha.add hb
  smul_mem' := fun c a ha => by
    show IsMixed M₁ H' (M.co.e.symm (hat (c • a)))
    rw [hat_smul, LinearEquiv.map_smul]
    exact ha.smul _

theorem mem_lagr {M : Model σ X W} {M₁ : Model σ X W₁} {H' : Plane E d d₁} {w} :
    w ∈ lagr M M₁ H' ↔ IsMixed M₁ H' (M.co.e.symm (hat w)) := Iff.rfl

theorem mul_transpose_injective : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n d d₁ : ℕ)
    (JW : Matrix (Fin d) (Fin d) E) (JW₁ : Matrix (Fin d₁) (Fin d₁) E) (ι : Matrix (Fin d) (Fin d₁) E),
    ιᵀ * JW * ι.map σ = JW₁ → JW₁.det ≠ 0 → Function.Injective fun z : Matrix (Fin n) (Fin d₁) E => z * ιᵀ := by
  intro F E _ _ _ σ n d d₁ JW JW₁ ι hg hdet z z' h
  simp only at h
  have h0 : (z - z') * JW₁ = 0 := by
    rw [← hg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.sub_mul, h, sub_self, Matrix.zero_mul, Matrix.zero_mul]
  have h1 : z - z' = 0 := by
    have := congrArg (· * JW₁⁻¹) h0
    simp only [Matrix.zero_mul] at this
    rwa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.mul_one] at this
  exact sub_eq_zero.mp h1

end GlobalTheory.MixedLagr

end
end

section

noncomputable section

namespace GlobalTheory.ThK.UnipDom

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def fA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w : Fin n → AE F E) : AE F E :=
  v ⬝ᵥ (incM F J *ᵥ fun i => cA σ (w i))

def coA (σ : E →ₐ[F] E) {d d₁ : ℕ} (J : Matrix (Fin d) (Fin d) E) (H' : Plane E d d₁) (g : UA σ J) :
    Fin d₁ → AE F E :=
  fun j => fA σ J (mat g *ᵥ (incM F H'.ι *ᵥ Pi.single j 1)) (incV F H'.y)

def coC (σ : E →ₐ[F] E) {d d₁ : ℕ} (J : Matrix (Fin d) (Fin d) E) (H' : Plane E d d₁) (g : UA σ J) : AE F E :=
  fA σ J (mat g *ᵥ incV F H'.y) (incV F H'.y)

end GlobalTheory.ThK.UnipDom
end
end

section

noncomputable section

namespace GlobalTheory.ThK.LemF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def IsLocPart {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    (M : Model σ X W) (M₁ : Model σ X₁ W₁) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁)
    (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁))
    (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ) : Prop :=
  ei ≠ 0 ∧ (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) ∧
    ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)

end GlobalTheory.ThK.LemF

end
end

section

noncomputable section

namespace GlobalTheory.ThK.EvUniq

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

def FinRel (B : Base F E) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (v : Pl F)
    (T : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d₁ → Fv F v) → ℂ) : Prop :=
  (∀ z, At (evFin F v) z → ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)) φ φ₁ →
      ∀ χ₁ ∈ SB (Fin n × Fin d₁ → Fv F v), Acts (evFin F v) (M₁.co.rho B.ψ z) (T φ) χ₁ → T φ₁ = χ₁) ∧
  ∀ u ∈ iso0 (F := F) n H', At (evFin F v) u → ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
    ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), Acts (evFin F v) (M.co.rho B.ψ u) φ φ₁ → T φ₁ = T φ

def InfRel (B : Base F E) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁)
    (T : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁)) : Prop :=
  (∀ z, At (evI F) z → ∀ f f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ)) f f₁ →
      ∀ g₁ : SInf F (Fin n × Fin d₁), Acts (evI F) (M₁.co.rho B.ψ z) (T f) g₁ → T f₁ = g₁) ∧
  ∀ u ∈ iso0 (F := F) n H', At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d),
    Acts (evI F) (M.co.rho B.ψ u) f f₁ → T f₁ = T f

end GlobalTheory.ThK.EvUniq
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixXChar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def dblEmb {n n₁ : ℕ} (ι : Matrix (Fin n) (Fin n₁) E) : Matrix (Fin n ⊕ Fin n) (Fin n₁ ⊕ Fin n₁) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
  Matrix.fromBlocks ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) ι) 0 0 ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) ι)

def isoD (d : ℕ) {n n₁ : ℕ} (H : Plane E n n₁) : Set (Matrix (Fin d) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :=
  {u | ∃ z₁ z₂ : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), u = Matrix.vecMulVec z₁ (Sum.elim (incV F H.x) (0 : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) +
    Matrix.vecMulVec z₂ (Sum.elim (0 : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (incV F H.x))}

def IsDLevi {n n₁ : ℕ} {J : Matrix (Fin n) (Fin n) E} {J₁ : Matrix (Fin n₁) (Fin n₁) E} (H : Plane E n n₁)
    (gd₁ : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) J₁))) (md : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) J))) : Prop :=
  md.1.1 *ᵥ Sum.elim (incV F H.x) (0 : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = Sum.elim (incV F H.x) (0 : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ∧
  md.1.1 *ᵥ Sum.elim (0 : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (incV F H.x) = Sum.elim (0 : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (incV F H.x) ∧
  md.1.1 * dblEmb H.ι = dblEmb H.ι * gd₁.1.1

def IsDblOf (ψ : AddChar (AF F) ℂ) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (χW : Chr F E)
    (om : Rep σ X W)
    (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d)))
    (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J)) →* Module.End ℂ (((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) → ℂ)) : Prop :=
  ∃ d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J)) (Fin n × Fin d), (∀ x, d'.e xᵀ = M.co.e x) ∧
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) d' dd ∧
    IsUWeilSplit (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J)) dd χW (diagCols (Fin n)) omd ∧
    ∀ (g : UA σ X.J) (gd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J))),
      gd.1.1 = Matrix.fromBlocks (mat g) 0 0 1 →
      ∀ φ₁ ∈ schA F (Fin n × Fin d), ∀ φ₂ ∈ schA F (Fin n × Fin d), omd gd (boxFun φ₁ φ₂) = boxFun (om (g, 1) φ₁) φ₂

theorem exists_isDblOf {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E}
    {om : Rep σ X W} {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s') :
    ∃ dd omd, IsDblOf B.ψ M χW om dd omd := by
  obtain ⟨-, ⟨d', hd', -, dd, omd, h1, h2, h3⟩, -⟩ := hP.weil
  exact ⟨dd, omd, d', hd', h1, h2, fun g gd hgd φ₁ h₁ φ₂ h₂ => h3 g gd hgd φ₁ h₁ φ₂ h₂⟩

end GlobalTheory.MixXChar

end
end
