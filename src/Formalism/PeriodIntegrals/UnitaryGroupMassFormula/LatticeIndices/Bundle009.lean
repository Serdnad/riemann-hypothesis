module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle007
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle003
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SecondSplitSmul
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle001
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace MassDataIdxK

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain Topology
open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

theorem isOpen_forall_mulVec {Λ U : Set (Fin n → Fv F v ⊗[F] E)} (hΛ : IsCompact Λ) (hU : IsOpen U) :
    IsOpen {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ U} := by
  have := fdFE (F := F) (E := E)
  have := MassDataIdxSteps.tens_topRing (F := F) (E := E) v
  rw [isOpen_iff_mem_nhds]
  intro A0 hA0
  exact hΛ.eventually_forall_of_forall_eventually fun y hy =>
    (continuous_fst.matrix_mulVec continuous_snd).continuousAt.preimage_mem_nhds (hU.mem_nhds (hA0 y hy))

theorem isCompact_stab (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (hfg : L.FG) :
    IsCompact {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ (latLoc (E := E) v (L : Set (Fin n → E)) :
      Set (Fin n → Fv F v ⊗[F] E)), A *ᵥ y ∈ (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E))} := by
  have := fdFE (F := F) (E := E)
  have := MassDataIdxSteps.tens_topRing (F := F) (E := E) v
  set Λ : Set (Fin n → Fv F v ⊗[F] E) := (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) with hΛ
  obtain ⟨m, b, hbΛ, hsp, -⟩ := latImage v L hL hfg
  obtain ⟨hΛo, hΛc⟩ := latOpenCompact v L hL hfg
  have hΛcl : IsClosed Λ :=
    AddSubgroup.isClosed_of_isOpen (latLoc (E := E) v (L : Set (Fin n → E))).toAddSubgroup hΛo
  have hclosed : IsClosed {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ Λ} := by
    have : {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ Λ} =
        ⋂ y ∈ Λ, (fun A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) => A *ᵥ y) ⁻¹' Λ := by
      ext A; simp
    rw [this]
    exact isClosed_biInter fun y _ => hΛcl.preimage (continuous_id.matrix_mulVec continuous_const)
  let Ψ : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin m → Fin n → Fv F v ⊗[F] E) :=
    { toFun := fun A i => A *ᵥ b i
      map_add' := fun A B => by funext i; exact Matrix.add_mulVec A B (b i)
      map_smul' := fun r A => by
        funext i j
        simp [Matrix.mulVec, dotProduct, Finset.smul_sum, smul_mul_assoc] }
  have hinj : LinearMap.ker Ψ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro A hA
    let Al : (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v] (Fin n → Fv F v ⊗[F] E) :=
      { toFun := fun x => A *ᵥ x
        map_add' := Matrix.mulVec_add A
        map_smul' := fun r x => Matrix.mulVec_smul A r x }
    have hAl : Al = 0 := LinearMap.ext_on_range hsp (fun i => congrFun hA i)
    ext i j
    have := congrFun (LinearMap.congr_fun hAl (Pi.single j 1)) i
    simpa [Al, Matrix.mulVec_single_one] using this
  obtain ⟨Ψ', hΨ'⟩ := LinearMap.exists_leftInverse_of_injective Ψ hinj
  have hc : Continuous Ψ' := IsModuleTopology.continuous_of_linearMap Ψ'
  have hsub : {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ Λ} ⊆
      Ψ' '' Set.pi Set.univ (fun _ => Λ) := by
    intro A hA
    exact ⟨Ψ A, fun i _ => hA _ (hbΛ i), by rw [← LinearMap.comp_apply, hΨ', LinearMap.id_apply]⟩
  exact ((isCompact_univ_pi fun _ => hΛc).image hc).of_isClosed_subset hclosed hsub

theorem kloc_open_compact (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (hfg : L.FG) :
    IsOpen (Kloc (E := E) v (L : Set (Fin n → E)) : Set (GL (Fin n) (Fv F v ⊗[F] E))) ∧
      IsCompact (Kloc (E := E) v (L : Set (Fin n → E)) : Set (GL (Fin n) (Fv F v ⊗[F] E))) := by
  have := fdFE (F := F) (E := E)
  have := MassDataIdxSteps.tens_topRing (F := F) (E := E) v
  have := t2Space_scalarTensorExt (F := F) (E := E) v
  set Λ : Set (Fin n → Fv F v ⊗[F] E) := (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) with hΛ
  set S := {A : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) | ∀ y ∈ Λ, A *ᵥ y ∈ Λ} with hS
  obtain ⟨hΛo, hΛc⟩ := latOpenCompact v L hL hfg
  have hSo : IsOpen S := isOpen_forall_mulVec v hΛc hΛo
  have hSc : IsCompact S := isCompact_stab v L hL hfg
  have heq : (Kloc (E := E) v (L : Set (Fin n → E)) : Set (GL (Fin n) (Fv F v ⊗[F] E))) =
      Units.embedProduct _ ⁻¹' (S ×ˢ (MulOpposite.unop ⁻¹' S)) := by
    ext g
    show (∀ x, x ∈ Λ ↔ (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ x ∈ Λ) ↔
      ((g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) ∈ S ∧
        ((g⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) ∈ S)
    constructor
    · intro hg
      refine ⟨fun y hy => (hg y).1 hy, fun y hy => ?_⟩
      have := (hg (((g⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) _) *ᵥ y)).2
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at this
      exact this hy
    · rintro ⟨h1, h2⟩ x
      refine ⟨h1 x, fun hx => ?_⟩
      have := h2 _ hx
      rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at this
  rw [heq]
  refine ⟨(hSo.prod (hSo.preimage MulOpposite.continuous_unop)).preimage
    Units.isEmbedding_embedProduct.continuous, ?_⟩
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hSc.prod ((MulOpposite.opHomeomorph.symm.isCompact_preimage).2 hSc))

def sigL (σ : E →ₐ[F] E) : (Fv F v ⊗[F] E) →ₗ[Fv F v] (Fv F v ⊗[F] E) where
  toFun := sigR (Fv F v) σ
  map_add' := map_add _
  map_smul' := fun r x => by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    rw [Algebra.TensorProduct.algebraMap_apply]
    show Algebra.TensorProduct.map (AlgHom.id F (Fv F v)) σ (algebraMap (Fv F v) (Fv F v) r ⊗ₜ 1) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl

theorem isClosed_HR (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) :
    IsClosed ((HR (Fv F v) σ J : Subgroup (GL (Fin n) (Fv F v ⊗[F] E))) : Set (GL (Fin n) (Fv F v ⊗[F] E))) := by
  have := fdFE (F := F) (E := E)
  have := MassDataIdxSteps.tens_topRing (F := F) (E := E) v
  have := t2Space_scalarTensorExt (F := F) (E := E) v
  have hσ : Continuous (sigR (F := F) (Fv F v) σ) := IsModuleTopology.continuous_of_linearMap (sigL v σ)
  have hval : Continuous (fun g : GL (Fin n) (Fv F v ⊗[F] E) => (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))) :=
    Units.continuous_val
  exact isClosed_eq (((hval.matrix_map hσ).matrix_transpose.matrix_mul continuous_const).matrix_mul hval)
    continuous_const

end MassDataIdxK
end
end

section

noncomputable section

namespace MassDataIdxSplit

open scoped TensorProduct

variable {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K]

def phi (σ : E →ₐ[F] E) (ι : E →ₐ[F] K) : K ⊗[F] E →ₐ[K] K × K :=
  Algebra.TensorProduct.lift (Algebra.ofId K (K × K)) (ι.prod (ι.comp σ)) (fun _ _ => Commute.all _ _)

theorem phi_tmul (σ : E →ₐ[F] E) (ι : E →ₐ[F] K) (x : K) (e : E) :
    phi σ ι (x ⊗ₜ[F] e) = (x * ι e, x * ι (σ e)) := by
  simp [phi, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Prod.algebraMap_apply]

theorem phi_bijective (σ : E →ₐ[F] E) (ι : E →ₐ[F] K) (h2 : Module.finrank F E = 2) (a : E) (ha : σ a ≠ a) :
    Function.Bijective (phi σ ι) := by
  have hne : ι a - ι (σ a) ≠ 0 := by
    intro h
    exact ha (ι.injective (sub_eq_zero.mp h)).symm
  have hsurj : Function.Surjective (phi σ ι) := by
    rintro ⟨u, v⟩
    refine ⟨((u - v) / (ι a - ι (σ a))) ⊗ₜ[F] a + (u - (u - v) / (ι a - ι (σ a)) * ι a) ⊗ₜ[F] (1 : E), ?_⟩
    rw [map_add (f := _), phi_tmul, phi_tmul]
    simp only [map_one, mul_one, Prod.mk_add_mk, Prod.mk.injEq]
    constructor
    · ring
    · field_simp
      ring
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  have hr : Module.finrank K (K ⊗[F] E) = Module.finrank K (K × K) := by
    rw [Module.finrank_baseChange, h2, Module.finrank_prod, Module.finrank_self]
  have key := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hr
    (f := (phi σ ι).toLinearMap)).mpr (by exact hsurj)
  exact ⟨by exact key, hsurj⟩

theorem phi_sig (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (ι : E →ₐ[F] K) (t : K ⊗[F] E) :
    phi σ ι (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR K σ t) = (phi σ ι t).swap := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x e =>
    simp only [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, phi_tmul, hσ, Prod.swap_prod_mk]
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
    rfl

end MassDataIdxSplit

namespace MassDataIdxSteps

open Formalism.L2.SG.TypedSets Formalism.L2.SG.HidaSetting

def EmbP {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (p : TypX X) : Prop :=
  Nonempty (X.B.I.E →ₐ[X.B.I.F] FpX X p)

theorem splitTheta_of {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (p : TypX X) (h : EmbP X p) :
    ∃ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ := by
  obtain ⟨ι⟩ := h
  have hσ : ∀ x, X.B.I.cm.sig (X.B.I.cm.sig x) = x := fun x => star_star x
  have h2 : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  have hex : ∃ a, X.B.I.cm.sig a ≠ a := by
    by_contra hne
    push_neg at hne
    have htop : (⊥ : Subalgebra X.B.I.F X.B.I.E) = ⊤ := by
      refine eq_top_iff.mpr fun x _ => Algebra.mem_bot.mpr ?_
      obtain ⟨y, hy⟩ := (X.B.I.cm.fixed x).1 (hne x)
      exact ⟨y, hy⟩
    have := Subalgebra.bot_eq_top_iff_finrank_eq_one.mp htop
    omega
  obtain ⟨a, ha⟩ := hex
  exact ⟨AlgEquiv.ofBijective (MassDataIdxSplit.phi X.B.I.cm.sig ι)
    (MassDataIdxSplit.phi_bijective _ ι h2 a ha), fun t => MassDataIdxSplit.phi_sig _ hσ ι t⟩

end MassDataIdxSteps
end
end

section

noncomputable section

namespace MassDataIdxRes

open NumberField IsDedekindDomain Ideal

private theorem comap_ringEquiv_ne_bot {A B : Type} [CommRing A] [CommRing B] (f : A ≃+* B)
    (I : Ideal B) (hI : I ≠ ⊥) : I.comap (f : A →+* B) ≠ ⊥ := by
  intro h
  apply hI
  ext y
  constructor
  · intro hy
    have h1 : f.symm y ∈ I.comap (f : A →+* B) := by
      rw [Ideal.mem_comap]
      simpa using hy
    rw [h, Ideal.mem_bot] at h1
    simpa using h1
  · intro hy
    rw [Ideal.mem_bot] at hy
    rw [hy]
    exact I.zero_mem

theorem split_transport {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (e : K ≃+* L)
    (l : ℕ) (h : {w : HeightOneSpectrum (𝓞 L) | ((l : ℕ) : 𝓞 L) ∈ w.asIdeal}.ncard = Module.finrank ℚ L) :
    {w : HeightOneSpectrum (𝓞 K) | ((l : ℕ) : 𝓞 K) ∈ w.asIdeal}.ncard = Module.finrank ℚ K := by
  classical
  have hrk : Module.finrank ℚ K = Module.finrank ℚ L :=
    (e.toRatAlgEquiv.toLinearEquiv).finrank_eq
  rw [hrk, ← h]
  let g : 𝓞 K ≃+* 𝓞 L := NumberField.RingOfIntegers.mapRingEquiv e
  refine Set.ncard_congr
    (fun w _ => (⟨w.asIdeal.comap (g.symm : 𝓞 L →+* 𝓞 K),
      (by haveI := w.isPrime; infer_instance),
      comap_ringEquiv_ne_bot g.symm w.asIdeal w.ne_bot⟩ : HeightOneSpectrum (𝓞 L))) ?_ ?_ ?_
  · intro w hw
    simp only [Set.mem_setOf_eq, Ideal.mem_comap] at hw ⊢
    simpa using hw
  · intro a b _ _ hab
    have h1 := congrArg HeightOneSpectrum.asIdeal hab
    apply HeightOneSpectrum.ext
    ext x
    have h2 := SetLike.ext_iff.mp h1 (g x)
    simpa [Ideal.mem_comap] using h2
  · intro w hw
    refine ⟨⟨w.asIdeal.comap (g : 𝓞 K →+* 𝓞 L), (by haveI := w.isPrime; infer_instance),
      comap_ringEquiv_ne_bot g w.asIdeal w.ne_bot⟩, ?_, ?_⟩
    · simp only [Set.mem_setOf_eq, Ideal.mem_comap] at hw ⊢
      simpa using hw
    · apply HeightOneSpectrum.ext
      ext x
      rw [Ideal.mem_comap, Ideal.mem_comap]
      simp

end MassDataIdxRes

namespace MassDataIdxSteps

open NumberField Formalism.L2.SG.TypedSets Formalism.L2.SG.HidaSetting

theorem resArith_holds {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (p : TypX X) : ResArith X p := by
  have hgp : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  have hmem : ((gOf p : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
    have hty := (mem_typSet X.B.I.F (D.host.g 0) (D.host.g 1) (D.host.g_prime 0).ne_zero
      (D.host.g_prime 1).ne_zero p.1).1 p.2
    unfold gOf
    split_ifs with h
    · exact h
    · exact hty.resolve_left h
  have hsplit : {w : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.E) |
      ((gOf p : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal}.ncard = Module.finrank ℚ X.B.I.E := by
    unfold gOf
    split_ifs
    · exact MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 0)
    · exact MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 1)
  obtain ⟨he, hf⟩ := MassDataIdxRes.locDeg_one_below (F := X.B.I.F) (E := X.B.I.E) (gOf p) hsplit p.1 hmem
  obtain ⟨hc, hn⟩ := MassDataIdxRes.arith_of_loc (gOf p) p.1 hmem he hf
  exact ⟨hc, hmem, hn⟩

theorem stResZ_holds {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (p : TypX X) : StResZ X p :=
  stResZ_of X p (resArith_holds X p)

end MassDataIdxSteps
end
end

section

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix

def CoreAll : Prop :=
  ∀ (K T : Type) [Field K] [CommRing T] [Algebra K T] (O : ValuationSubring K) (n : Type) [Fintype n]
    [DecidableEq n] (θ : T ≃ₐ[K] K × K) (s : T →+* T) (J : Matrix n n T) (P : GL n K),
    (∀ t, θ (s t) = (θ t).swap) → Formalism.UG.cT s J = J → IsUnit J.det →
    MassDataIdxCore.KerBack O θ s J P ∧ MassDataIdxCore.SurjCore O θ s J P

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X)

theorem herm_JR : Formalism.UG.cT (sigR (FpX X p) X.B.I.cm.sig) (JR (FpX X p) X.B.I.J) = JR (FpX X p) X.B.I.J := by
  have hJ := X.B.I.J_herm
  unfold Formalism.UG.IsHerm at hJ
  ext i j
  have h1 := congrFun (congrFun hJ i) j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at h1 ⊢
  simp only [JR, Matrix.map_apply, sigR, inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rw [← h1]
  rfl

theorem unit_JR : IsUnit (JR (F := X.B.I.F) (FpX X p) X.B.I.J).det := by
  have h1 : (JR (F := X.B.I.F) (FpX X p) X.B.I.J).det = inclR (F := X.B.I.F) (FpX X p) X.B.I.J.det := by
    unfold JR
    rw [RingHom.map_det]
    rfl
  rw [h1]
  exact (isUnit_iff_ne_zero.mpr X.B.I.J_det).map _

end Loc

theorem latCore_of (hC : CoreAll) : LatCore := by
  intro D X p θ hθ P hP K hK
  obtain ⟨hKB, hSU⟩ := hC (FpX X p) (TpX X p) (p.1.adicCompletionIntegers X.B.I.F) (Fin X.B.I.n) θ
    (sigR (FpX X p) X.B.I.cm.sig) (JR (FpX X p) X.B.I.J) P hθ (herm_JR X p) (unit_JR X p)
  have hLat : ∀ x, x ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) ↔
      x ∈ MassDataIdxCore.Lat (p.1.adicCompletionIntegers X.B.I.F) θ (JR (FpX X p) X.B.I.J) P := hP
  let m : K →* GL (Fin X.B.I.n) (TpX X p) :=
    (HR (FpX X p) X.B.I.cm.sig X.B.I.J).subtype.comp K.subtype
  have hmem : ∀ h : K, HA.mat (FpX X p) X.B.I.cm.sig X.B.I.J (h : HAp X p) ∈
      Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
    intro h
    have : (h : HAp X p) ∈ (K : Set (HAp X p)) := h.2
    rw [hK] at this
    exact this
  have hKl : ∀ h x, x ∈ MassDataIdxCore.Lat (p.1.adicCompletionIntegers X.B.I.F) θ (JR (FpX X p) X.B.I.J) P ↔
      ((m h : GL (Fin X.B.I.n) (TpX X p)) : Matrix _ _ (TpX X p)) *ᵥ x ∈
        MassDataIdxCore.Lat (p.1.adicCompletionIntegers X.B.I.F) θ (JR (FpX X p) X.B.I.J) P := by
    intro h x
    rw [← hLat, ← hLat]
    exact hmem h x
  have hon : ∀ g : GL (Fin X.B.I.n) (TpX X p), g ∈ Formalism.UG.UJ (sigR (FpX X p) X.B.I.cm.sig) (JR (FpX X p) X.B.I.J) →
      (∀ x, x ∈ MassDataIdxCore.Lat (p.1.adicCompletionIntegers X.B.I.F) θ (JR (FpX X p) X.B.I.J) P ↔
        (g : Matrix _ _ (TpX X p)) *ᵥ x ∈ MassDataIdxCore.Lat (p.1.adicCompletionIntegers X.B.I.F) θ
          (JR (FpX X p) X.B.I.J) P) → ∃ h, m h = g := by
    intro g hg hgs
    let x0 : HAp X p := ⟨g, hg⟩
    have hin : x0 ∈ K := by
      rw [← SetLike.mem_coe, hK]
      show g ∈ Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))
      intro x
      rw [hLat, hLat]
      exact hgs x
    exact ⟨⟨_, hin⟩, rfl⟩
  obtain ⟨ψ, hψ, hker⟩ := MassDataIdxCore.latGL_gen (p.1.adicCompletionIntegers X.B.I.F) θ
    (sigR (FpX X p) X.B.I.cm.sig) (JR (FpX X p) X.B.I.J) P hKB hSU ((gOf p : ℕ) : Op X p) m (fun h => (h : HAp X p).2)
    hKl hon
  refine MassDataIdxCore.reindex_gl (idxEquiv X) _ _ ψ hψ (fun h => ?_)
  rw [hker h]
  have hsm : ∀ z : Fin X.B.I.n → TpX X p,
      (((gOf p : ℕ) : Op X p) : FpX X p) • z = ((gOf p : ℕ) : Op X p) • z := fun z => rfl
  constructor
  · intro H0
    refine ⟨(hmem h), fun y hy => ?_⟩
    obtain ⟨z, hz, hz'⟩ := H0 y ((hLat y).1 hy)
    exact ⟨z, (hLat z).2 hz, by rw [← hsm]; exact hz'⟩
  · rintro ⟨-, H0⟩ y hy
    obtain ⟨z, hz, hz'⟩ := H0 y ((hLat y).2 hy)
    exact ⟨z, (hLat z).1 hz, by rw [hsm]; exact hz'⟩

theorem stRed_of_core {D : D7} (X : HidaSetting D) (p : TypX X) (hR : StResZ X p) (hS : StSplitLat X p)
    (hC : CoreAll) : StRed X p := stRed_of_parts X p hR hS (latCore_of hC)

end MassDataIdxSteps
end
end
