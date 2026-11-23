module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1733
public import Development.WeilBound.ThetaLifts.ConeHypotheses.PolDense
public import Development.WeilBound.ThetaLifts.LatticeBasics.ExistsIsGauss
public import Development.WeilBound.ThetaLifts.LatticeBasics.BoxFinB
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle015
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.Bundle001
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.EqZeroOfPiInf
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.ExistsAdelePiInf
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.Bundle004
import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.HeckeBridge GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds
open GlobalTheory.CMVal (IsHeckeL IsCMType eulerFactor)

theorem exists_hchar_unitary (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) : IsCMExt F E σ → ∀ χ : Chr F E, IsHecke F E χ → ∃ H : Formalism.L2.Host.HChar E, H.IsUnitary ∧
      (∀ (W : HeightOneSpectrum (𝓞 E)) (x : (W.adicCompletion E)ˣ), H.loc W x = locChar χ W x) ∧
      ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (m : InfinitePlace F → ℤ), HasExp τ χ m →
        H.HasInf (fun w => (τ w).1) m := by
  intro hcm χ hχ
  obtain ⟨Φ, j, -, hΦc, hj, hΦ⟩ := exists_tensor_adele_equiv F E σ hcm
  have hfin : ∀ x : E, finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = algebraMap E (FiniteAdeleRing (𝓞 E) E) x := fun x => by
    rw [show finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = _ from toFinAd_tmul 1 x, map_one, one_mul]
  let u : Neutral.B1.Ideles E →* (AF F ⊗[F] E)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΦc
  have ht : Continuous (Circle.toUnits : Circle →* ℂˣ) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, by
      have h : Continuous fun z : Circle => ((z⁻¹ : Circle) : ℂ) := continuous_subtype_val.comp continuous_inv
      refine h.congr fun z => ?_
      simp⟩
  have hdiag : ∀ k : Eˣ, u (Neutral.B1.diagUnits E k) = Units.map (inclR (F := F) (AF F)).toMonoidHom k := fun k =>
    Units.ext (Φ.symm_apply_eq.2 (by
      rw [hΦ]
      change (algebraMap E (InfiniteAdeleRing E) k, algebraMap E (FiniteAdeleRing (𝓞 E) E) k) = _
      refine Prod.ext (hj k).symm (hfin k).symm))
  have hloc : ∀ (W : HeightOneSpectrum (𝓞 E)) (x : (W.adicCompletion E)ˣ),
      u (Neutral.B1.localIdele E W x) = locIdele F W x := fun W x =>
    Units.ext (Φ.symm_apply_eq.2 (by
      rw [hΦ, infTens_locIdele, map_one, finTens_locIdele]
      rfl))
  let H : Formalism.L2.Host.HChar E := ⟨Circle.toUnits.comp (χ.comp u), ht.comp (hχ.1.comp hu), fun k => by
    change Circle.toUnits (χ (u _)) = 1
    rw [hdiag, hχ.2, map_one]⟩
  refine ⟨H, fun x => Circle.norm_coe (χ (u x)), fun W x => ?_, fun τ m hm k => ?_⟩
  · change Circle.toUnits (χ (u _)) = Circle.toUnits (χ (locIdele F W x))
    rw [hloc]
  · set z := u (Formalism.L2.Host.infDiag k) with hz
    have hz1 : Φ (z : AF F ⊗[F] E) = (Formalism.L2.Host.infDiag k : AdeleRing (𝓞 E) E) := Φ.apply_symm_apply _
    rw [coe_infDiag, hΦ] at hz1
    have hinf : infTens F E z = (1 : Ainf F) ⊗ₜ[F] (k : E) :=
      j.injective ((congrArg Prod.fst hz1).trans (hj k).symm)
    have hfin1 : finTens F E z = 1 :=
      (finAdEquiv F E).injective ((congrArg Prod.snd hz1).trans (map_one _).symm)
    have hAt : At (evI F) ((z : AF F ⊗[F] E) - 1) := by
      intro a ha
      have ha1 : a.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (ha.trans (map_zero _).symm)
      refine tens_ext ?_ ?_
      · rw [Algebra.smul_def, map_mul, map_zero]
        change (a.1 ⊗ₜ[F] (1 : E)) * _ = 0
        rw [ha1, TensorProduct.zero_tmul, zero_mul]
      · rw [Algebra.smul_def, map_mul, map_zero, map_sub, map_one, hfin1, sub_self, mul_zero]
    have hpi : ∀ w, piInf (τ w) z = (τ w).1 k := fun w => by
      change infEmb (τ w) (compInf F E w z) = _
      rw [compInf_eq_infTens, hinf, Algebra.TensorProduct.map_tmul, map_one, infEmb_tmul, map_one, one_mul]
      rfl
    change ((χ z : Circle) : ℂ) = _
    rw [hm z hAt]
    exact Finset.prod_congr rfl fun w _ => by rw [hpi w]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isCMType_emb (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) : IsCMType fun w => (τ w).1 := by
  haveI := h.1
  haveI := h.2.1
  haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩
  have real : ∀ φ : F →+* ℂ, ComplexEmbedding.conjugate φ = φ := fun φ => IsTotallyReal.complexEmbedding_isReal φ
  have emb : ∀ φ : F →+* ℂ, (InfinitePlace.mk φ).embedding = φ := fun φ =>
    (InfinitePlace.embedding_mk_eq φ).elim id fun e => e.trans (real φ)
  intro φ
  have cj : ∀ w, (ComplexEmbedding.conjugate (τ w).1).comp (algebraMap F E) = w.embedding := fun w =>
    (congrArg ComplexEmbedding.conjugate (τ w).2).trans (real _)
  refine ⟨InfinitePlace.mk (φ.comp (algebraMap F E)), ?_, fun w hw => ?_⟩
  · set w := InfinitePlace.mk (φ.comp (algebraMap F E))
    obtain ⟨g, hg⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := F) (τ w).1 φ ((τ w).2.trans (emb _))
    let s : E ≃ₐ[F] E := AlgEquiv.ofBijective σ σ.bijective
    have hs : s ≠ 1 := fun e => IsTotallyComplex.complexEmbedding_not_isReal φ (RingHom.ext fun x => by
      have e1 : σ x = x := congrArg (fun y : E ≃ₐ[F] E => y x) e
      have := h.2.2.2 φ x
      rw [e1] at this
      exact this.symm)
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 ((IsGalois.card_aut_eq_finrank F E).trans h.2.2.1)
    by_cases e : g.symm = 1
    · left; rw [← hg, e]; rfl
    · right
      rw [← hg, (hy _ e).trans (hy _ hs).symm]
      exact RingHom.ext fun x => h.2.2.2 _ x
  · rcases hw with rfl | rfl
    · rw [(τ w).2, InfinitePlace.mk_embedding]
    · rw [cj, InfinitePlace.mk_embedding]

variable {I : Type} [Fintype I]

theorem eq_charL {χ : Chr F E} {H : Formalism.L2.Host.HChar E} (hu : H.IsUnitary) (hloc : ∀ W x, H.loc W x = locChar χ W x)
    {L : ℂ → ℂ} (hL : IsHeckeL H L) {s : ℂ} (hs : 1 < s.re) : L s = charL χ (∅ : Set (Pl F)) s := by
  have e : charFam χ = heckeFam H := funext fun w => by
    have e1 : UnrAt χ w ↔ H.UnrAt w := forall₂_congr fun x _ => by rw [hloc]
    have e2 : val χ w = H.val w := (hloc _ _).symm
    by_cases hw : H.UnrAt w <;> simp [charFam, heckeFam, e1, e2, hw]
  have e0 : above E (∅ : Set (Pl F)) = ∅ := Set.eq_empty_of_forall_notMem fun _ h => h
  rw [charL, LS, e, e0]
  have h1 := (converges_heckeFam ∅ hu hs).hasProd
  simp only [locL_heckeFam] at h1
  exact (hL.2 s hs).unique ((Equiv.subtypeUnivEquiv (p := fun w => w ∉ (∅ : Set (HeightOneSpectrum (𝓞 E))))
    (fun _ => Set.notMem_empty _)).hasProd_iff.1 h1)

def LInt2 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' → ∀ χ ∈ ({X.ν, X.ν⁻¹} : Set (Chr F E)),
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ (∀ s : ℂ, 1 < s.re → Λ s = charL χ (∅ : Set (Pl F)) s) ∧
      ∀ z : ℤ, -((a + a' : ℕ) : ℤ) ≤ 2 * z → Λ z ≠ 0

end GlobalTheory.ThK.Dbl

end
end

section

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem polDense : PositivityTheory.ThKG.PolDense := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have h0 := fun T hT => Dense.pol_dense M hP.base hP.herm hP.skew T hT
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  by_contra hnd
  obtain ⟨x, hx⟩ : ∃ x, x ∉ (M.Pol B.ψ B.emb).topologicalClosure := by
    by_contra h
    push Not at h
    exact hnd (eq_top_iff.2 fun x _ => h x)
  obtain ⟨f, u, hfs, hfx⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
    (((M.Pol B.ψ B.emb).topologicalClosure.restrictScalars ℝ).convex)
    (M.Pol B.ψ B.emb).isClosed_topologicalClosure hx
  have hf0 : ∀ a ∈ (M.Pol B.ψ B.emb).topologicalClosure, f a = 0 := by
    intro a ha
    by_contra hne
    have hmem : ((((|u| + 1 : ℝ) : ℂ) / f a) • a) ∈ (M.Pol B.ψ B.emb).topologicalClosure :=
      (M.Pol B.ψ B.emb).topologicalClosure.smul_mem _ ha
    have hlt := hfs _ hmem
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at hlt
    simp at hlt <;> linarith [le_abs_self u]
  have hfz : f = 0 := h0 f (fun g hg => hf0 g ((M.Pol B.ψ B.emb).le_topologicalClosure hg))
  have h00 := hfs 0 (Submodule.zero_mem _)
  rw [hfz] at hfx
  simp at hfx h00
  linarith

end GlobalTheory.ThK.Dbl

end
end

section

noncomputable section

namespace GlobalTheory.ThK.Dbl.Box

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.ThK.Dbl.Dense
open GlobalTheory.AdelicU (EmbOver)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (AE At SInf evI piInf realAd)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {κ β : Type} [Fintype κ] [Fintype β] {m n : ℕ}

theorem at_entry' {α β : Type} {u : Matrix α β (AE F E)} (hu : At (evI F) u) (i : α) (j : β) :
    At (evI F) (u i j) := fun c hc => by
  simpa using congrFun (congrFun (hu c hc) i) j

theorem exists_real_structure' (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (emb : ∀ w : InfinitePlace F, EmbOver E w)
    {α β : Type} {κ : Type} [Fintype κ]
    (e : Matrix α β (AE F E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F))
    (C : InfinitePlace F → Matrix α β ℂ →ₗ[ℝ] Matrix α β ℂ) :
    ∃ (s : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) →
          Matrix α β (AE F E))
      (Jm : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
        ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))),
      (∀ p, At (evI F) (s p)) ∧
      (∀ p, (fun i => evI F ((e (s p)).1 i)) = p.1 ∧ (fun i => evI F ((e (s p)).2 i)) = p.2) ∧
      ∀ p w, (s (Jm p)).map (piInf (emb w)) = C w ((s p).map (piInf (emb w))) := by
  let s : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) →
      Matrix α β (AE F E) :=
    fun p => e.symm (fun i => lift (p.1 i), fun i => lift (p.2 i))
  have es : ∀ p, e (s p) = (fun i => lift (p.1 i), fun i => lift (p.2 i)) := fun p => e.apply_symm_apply _
  have sAdd : ∀ p q, s (p + q) = s p + s q := fun p q => by
    show e.symm _ = e.symm _ + e.symm _
    rw [← map_add (f := _)]
    congr 1
    refine Prod.ext (funext fun i => lift_add _ _) (funext fun i => lift_add _ _)
  have sSmul : ∀ (t : ℝ) p, s (t • p) = realAd F t • s p := fun t p => by
    show e.symm _ = realAd F t • e.symm _
    rw [← map_smul]
    congr 1
    refine Prod.ext (funext fun i => lift_smul _ _) (funext fun i => lift_smul _ _)
  have sAt : ∀ p, At (evI F) (s p) := fun p c hc => by
    show c • e.symm _ = 0
    rw [← map_smul]
    have : c • ((fun i => lift (p.1 i), fun i => lift (p.2 i)) : (κ → AF F) × (κ → AF F)) = 0 :=
      Prod.ext (funext fun i => at_lift _ c hc) (funext fun i => at_lift _ c hc)
    rw [this, map_zero]
  let Ψ : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      (InfinitePlace F → Matrix α β ℂ) :=
    { toFun := fun p w => (s p).map (piInf (emb w))
      map_add' := fun p q => by
        funext w
        rw [sAdd]
        ext i j
        simp
      map_smul' := fun t p => by
        funext w
        rw [sSmul]
        ext i j
        simp [GlobalTheory.CompanionTheory.RealAdeleComponent.piInf_realAd_smul] }
  have hΨ : ∀ p w, Ψ p w = (s p).map (piInf (emb w)) := fun _ _ => rfl
  have inj : Function.Injective Ψ := by
    refine (injective_iff_map_eq_zero Ψ).2 fun p hp => ?_
    have s0 : s p = 0 := by
      ext i j
      refine GlobalTheory.CompanionTheory.CMAdele.eq_zero_of_piInf σ h emb _ (at_entry' (sAt p) i j) fun w => ?_
      have := congrFun (congrFun (congrFun hp w) i) j
      simpa [hΨ] using this
    have e0 := es p
    rw [s0, map_zero] at e0
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · have := congrFun (congrArg Prod.fst e0) i
      have := congrArg (evI F) this
      rw [evI_lift] at this
      simpa [evI_zero] using this.symm
    · have := congrFun (congrArg Prod.snd e0) i
      have := congrArg (evI F) this
      rw [evI_lift] at this
      simpa [evI_zero] using this.symm
  have surj : Function.Surjective Ψ := fun Z => by
    choose x hxA hxZ using fun (ij : α × β) => GlobalTheory.CompanionTheory.RealPlaceAdele.exists_adele_piInf σ h emb (fun w => Z w ij.1 ij.2)
    let u : Matrix α β (AE F E) := Matrix.of fun i j => x (i, j)
    have uAt : At (evI F) u := fun c hc => by
      ext i j
      exact hxA (i, j) c hc
    have hAt2 : ∀ c : AF F, evI F c = 0 → c • e u = 0 := fun c hc => by
      rw [← map_smul, uAt c hc, map_zero]
    refine ⟨(fun i => evI F ((e u).1 i), fun i => evI F ((e u).2 i)), ?_⟩
    have su : s (fun i => evI F ((e u).1 i), fun i => evI F ((e u).2 i)) = u := by
      show e.symm _ = u
      rw [LinearEquiv.symm_apply_eq]
      refine Prod.ext (funext fun i => lift_evI fun c hc => ?_) (funext fun i => lift_evI fun c hc => ?_)
      · exact congrFun (congrArg Prod.fst (hAt2 c hc)) i
      · exact congrFun (congrArg Prod.snd (hAt2 c hc)) i
    funext w
    rw [hΨ, su]
    ext i j
    exact hxZ (i, j) w
  let Ψe := LinearEquiv.ofBijective Ψ ⟨inj, surj⟩
  let Cp : (InfinitePlace F → Matrix α β ℂ) →ₗ[ℝ] (InfinitePlace F → Matrix α β ℂ) :=
    LinearMap.pi fun w => C w ∘ₗ LinearMap.proj w
  refine ⟨s, Ψe.symm.toLinearMap ∘ₗ Cp ∘ₗ Ψ, sAt, fun p => ?_, fun p w => ?_⟩
  · rw [es]
    exact ⟨funext fun i => evI_lift _, funext fun i => evI_lift _⟩
  · have : Ψ ((Ψe.symm.toLinearMap ∘ₗ Cp ∘ₗ Ψ) p) = Cp (Ψ p) := Ψe.apply_symm_apply _
    exact congrFun this w

def Rel (τ : ∀ w : InfinitePlace F, EmbOver E w) (ε : InfinitePlace F → ℤˣ) (θ : InfinitePlace F → Matrix (Fin m) (Fin m) ℂ)
    (θ' : InfinitePlace F → Matrix β β ℂ) (u u' : Matrix (Fin m) β (AE F E)) : Prop :=
  ∀ w, u'.map (piInf (τ w)) = (((ε w : ℤ) : ℂ) * Complex.I) • (θ w * u.map (piInf (τ w)) * (θ' w)ᵀ)

def dd0 (p : (κ → AF F) × (κ → AF F)) (f : SInf F κ) : SInf F κ := dop (nf p.1) (GlobalTheory.ThK.Dbl.Dense.linForm (nf p.2)) f

def Gs (e : Matrix (Fin m) β (AE F E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F)) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (ε : InfinitePlace F → ℤˣ) (θ : InfinitePlace F → Matrix (Fin m) (Fin m) ℂ) (θ' : InfinitePlace F → Matrix β β ℂ)
    (f : SInf F κ) : Prop :=
  ∀ u u', At (evI F) u → At (evI F) u' → Rel τ ε θ θ' u u' → dd0 (e u') f = Complex.I • dd0 (e u) f

variable {e : Matrix (Fin m) β (AE F E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F)} {τ : ∀ w : InfinitePlace F, EmbOver E w}
  {ε ε' : InfinitePlace F → ℤˣ} {θ : InfinitePlace F → Matrix (Fin m) (Fin m) ℂ} {θ' : InfinitePlace F → Matrix β β ℂ}
  {f f' : SInf F κ}

theorem Gs.gau (h : IsCMExt F E σ) (hf : Gs e τ ε θ θ' f) (h0 : f ≠ 0) : ∃ k, Gau f k := by
  let C : InfinitePlace F → Matrix (Fin m) β ℂ →ₗ[ℝ] Matrix (Fin m) β ℂ := fun w =>
    { toFun := fun x => (((ε w : ℤ) : ℂ) * Complex.I) • (θ w * x * (θ' w)ᵀ)
      map_add' := fun x y => by rw [Matrix.mul_add, Matrix.add_mul, smul_add]
      map_smul' := fun t x => by
        simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]
        rw [smul_comm] }
  obtain ⟨S, J, sAt, sev, sJ⟩ := exists_real_structure' σ h τ e C
  let T : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun y b => GlobalTheory.ThK.Dbl.Dense.linForm b y) (fun y y' b => map_add _ y y') (fun t y b => map_smul _ t y)
      (fun y b b' => by simp only [GlobalTheory.ThK.Dbl.Dense.linForm_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)])
      (fun t y b => by simp only [GlobalTheory.ThK.Dbl.Dense.linForm_apply, Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul])
  obtain ⟨k, hk⟩ := GlobalTheory.CompanionTheory.Twist.FockLogDeriv.main T (fun b hb => funext fun i => trace_mul_eq_zero _ fun y => by
      have : GlobalTheory.ThK.Dbl.Dense.linForm b (Pi.single i y) = 0 := hb _
      rw [GlobalTheory.ThK.Dbl.Dense.linForm_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same, mul_comm] at this
      exact this) J f h0 fun p y => by
    have := congrArg (fun g : SInf F κ => g y) (hf (S p) (S (J p)) (sAt _) (sAt _) fun w => sJ p w)
    have e1 : ∀ q, nf (e (S q)).1 = q.1 := fun q => (sev q).1
    have e2 : ∀ q, nf (e (S q)).2 = q.2 := fun q => (sev q).2
    simp only [dd0, SchwartzMap.smul_apply, smul_eq_mul, dop_apply, e1, e2] at this
    exact this
  exact ⟨k, gau_of h0 hk⟩

theorem exists_rel (h : IsCMExt F E σ) (ε : InfinitePlace F → ℤˣ) (u : Matrix (Fin m) β (AE F E)) :
    ∃ u', At (evI F) u' ∧ Rel τ ε θ θ' u u' := by
  choose x hx hz using fun i j => GlobalTheory.CompanionTheory.RealPlaceAdele.exists_adele_piInf σ h τ fun w =>
    ((((ε w : ℤ) : ℂ) * Complex.I) • (θ w * u.map (piInf (τ w)) * (θ' w)ᵀ)) i j
  exact ⟨Matrix.of x, fun c hc => Matrix.ext fun i j => hx i j c hc, fun w => Matrix.ext fun i j => hz i j w⟩

theorem Gs.same (h : IsCMExt F E σ) (hf : Gs e τ ε θ θ' f) (hf' : Gs e τ ε' θ θ' f') (h0 : f ≠ 0) (h0' : f' ≠ 0) :
    Gs e τ ε θ θ' f' := by
  intro u u' hu hu' hr
  obtain ⟨k, g⟩ := hf.gau h h0
  obtain ⟨k', g'⟩ := hf'.gau h h0'
  obtain ⟨u'', hu'', hr'⟩ := exists_rel (τ := τ) (θ := θ) (θ' := θ') h ε' u
  have hv : At (evI F) (u' - u'') := fun c hc => by rw [smul_sub, hu' c hc, hu'' c hc, sub_zero]
  obtain ⟨v', hv', hs⟩ := exists_rel (τ := τ) (θ := θ) (θ' := θ') h ε (u' - u'')
  have hs' : Rel τ ε' θ θ' (u' - u'') (-v') := fun w => by
    rw [Matrix.map_neg _ (map_neg _), hs w, Matrix.map_sub _ (map_sub _), hr w, hr' w, ← sub_smul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, ← neg_smul]
    congr 1
    rcases Int.units_eq_one_or (ε w) with a | a <;> rcases Int.units_eq_one_or (ε' w) with b | b <;> simp [a, b]
  have h2 := hf' _ _ hv (fun c hc => by rw [smul_neg, hv' c hc, neg_zero]) hs'
  have en : ∀ z : κ → AF F, nf (-z) = -nf z := fun z => funext fun i =>
    map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) (z i).1
  have el : ∀ b : κ → mixedEmbedding.mixedSpace F, GlobalTheory.ThK.Dbl.Dense.linForm (-b) = -GlobalTheory.ThK.Dbl.Dense.linForm b := fun b => by
    exact ContinuousLinearMap.ext fun y => by
      simp only [GlobalTheory.ThK.Dbl.Dense.linForm_apply, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, map_neg, ContinuousLinearMap.neg_apply]
  rw [map_neg, dd0, Prod.fst_neg, Prod.snd_neg, en, en, el] at h2
  obtain ⟨a0, l0⟩ := opp g g' (hf _ _ hv hv' hs) h2
  rw [← hf' u u'' hu hu'' hr', ← sub_add_cancel u' u'', map_add (f := _), dd0, Prod.fst_add, Prod.snd_add, nf_add, nf_add,
    linForm_add, a0, l0, zero_add, zero_add, dd0]

end GlobalTheory.ThK.Dbl.Box

end
end
