module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle059
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle135
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle084
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle085
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle112
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle025
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle002
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle068
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle051
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle136
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle127
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle118
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle067
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle119
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle137
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle069
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle102
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle131
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle084
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle122
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle074
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle138
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
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle008
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle134
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem reads_orbit_invFrob : ∀ (D : D7) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL) (c : D.host.E →+* ↥K.1) (κ : D.host.E →+* ↥LL.1), l ∉ D.host.small → l ≠ D.host.q → l ≠ D.host.d → (K.1 : Set (Om l)) ⊆ closure (Set.range fun x => ((c x : ↥K.1) : Om l)) → K.1 ≤ MaximalUnramifiedExtension l → ∃ g : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → D.R.GG, IsOrbit g (DV.frobG D l)⁻¹ ∧ ∀ τ a, Over W τ a → Reads D.host c κ τ (g a) := by
  intro D l _ P K LL W c κ h2 hq hd hcl hK
  set φ := DV.frobG D l with hφ
  set n := Module.finrank ℚ_[l] ↥(K0 K) with hn
  have hτ := fun a => GlobalTheory.T.existsUnique_embeddingRestrictsToWachLetter_unramified P K LL W hK a
  have hg := fun τ => GlobalTheory.T.existsUnique_embeddingReadsGaloisElement D.host K LL c κ τ
  let τa : ZMod n → (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := fun a => (hτ a).exists.choose
  have hover : ∀ a, Over W (τa a) a := fun a => (hτ a).exists.choose_spec
  let g : ZMod n → D.R.GG := fun a => (hg (τa a)).exists.choose
  have hread : ∀ a, Reads D.host c κ (τa a) (g a) := fun a => (hg (τa a)).exists.choose_spec
  have smul : ∀ u v : D.R.GG, D.host.sigmaOf (u * v) = D.host.sigmaOf u * D.host.sigmaOf v :=
    fun u v => map_mul (D.host.gal).symm u v
  have hK0 : K0 K = K.1 := inf_eq_left.mpr hK

  have step : ∀ a, g (a + 1) = g a * φ⁻¹ := by
    intro a
    refine (hg (τa (a + 1))).unique (hread (a + 1)) ?_
    intro z
    set x := D.host.sigmaOf φ⁻¹ z with hx
    have hz : D.host.sigmaOf φ x = z := by
      rw [hx, ← AlgEquiv.mul_apply, ← smul, mul_inv_cancel]
      show (D.host.gal).symm 1 z = z
      rw [map_one]; rfl
    let y : ↥(K0 K) := ⟨((c x : ↥K.1) : Om l), ⟨(c x).2, hK (c x).2⟩⟩
    have hy : algebraMap ↥(K0 K) ↥K.1 y = c x := Subtype.ext rfl
    have hσ := GlobalTheory.T.periodDatum_frobenius_restrict_hostField D P K c h2 hq hd x y hy
    have ov : ∀ b (t : ↥(K0 K)), τa b (algebraMap ↥(K0 K) ↥K.1 t) = W.emb b t := by
      intro b t
      have := congrArg (fun f => f t) (hover b)
      simpa using this
    have hemb : W.emb (a + 1) ((P.PD K).σ y) = W.emb a y := by
      have := congrArg (fun f => f y) (W.emb_σ a)
      simpa using this
    calc τa (a + 1) (c z) = τa (a + 1) (c (D.host.sigmaOf φ x)) := by rw [hz]
      _ = τa (a + 1) (algebraMap ↥(K0 K) ↥K.1 ((P.PD K).σ y)) := by rw [hσ]
      _ = W.emb (a + 1) ((P.PD K).σ y) := ov _ _
      _ = W.emb a y := hemb
      _ = τa a (algebraMap ↥(K0 K) ↥K.1 y) := (ov _ _).symm
      _ = τa a (c x) := by rw [hy]
      _ = κ (D.host.sigmaOf (g a) x) := hread a x
      _ = κ (D.host.sigmaOf (g a * φ⁻¹) z) := by rw [smul, AlgEquiv.mul_apply]

  have hfr : n = Module.finrank ℚ_[l] ↥K.1 := by
    rw [hn]; exact (IntermediateField.equivOfEq hK0).toLinearEquiv.finrank_eq
  have hlen : n = orderOf φ⁻¹ := by
    rw [orderOf_inv]
    obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
      (Ideal.span {(l : ℤ)}) (⊥ : Ideal (𝓞 D.host.E)) (by
        intro x hx
        simp only [Ideal.mem_comap, Ideal.mem_bot] at hx
        have : x = 0 := (algebraMap ℤ (𝓞 D.host.E)).injective_int (by simpa using hx)
        rw [this]; exact Ideal.zero_mem _)
    have := hQ
    have : Q.LiesOver (Ideal.span {(l : ℤ)}) := ⟨hQc.symm⟩
    have hfrob := (GlobalTheory.T.frobG_isArithFrobAt_and_sign_eq_jacobiSym D l h2 hq hd).1 Q
    let c' : D.host.E →+* PadicAlgCl l := (K.1.val : ↥K.1 →ₐ[ℚ_[l]] Om l).toRingHom.comp c
    have hc' : ∀ x, c' x ∈ K.1 := fun x => (c x).2
    have hcl' : (K.1 : Set (PadicAlgCl l)) ⊆ closure (Set.range c') := hcl
    have := (GlobalTheory.T.completion_embeddings_single_frobenius_orbit D.host l h2 hq hd c' K hc' hcl' Q (D.host.sigmaOf φ) hfrob).1
    have hφg : D.host.galE (D.host.sigmaOf φ) = φ :=
      (D.host.gal).apply_symm_apply φ
    rw [hfr, this, hφg]
  have hpos : 0 < n := by
    rw [hfr]
    have := K.2
    exact Module.finrank_pos
  have : NeZero n := ⟨hpos.ne'⟩
  refine ⟨g, ⟨hlen, ?_⟩, ?_⟩
  · have hk : ∀ k : ℕ, g (k : ZMod n) = g 0 * φ⁻¹ ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Nat.cast_succ, step, ih]
        exact (mul_assoc _ _ _).trans (congrArg _ (pow_succ φ⁻¹ k).symm)
    intro a
    have := hk a.val
    rwa [ZMod.natCast_zmod_val] at this
  · intro τ a h
    have : τ = τa a := (hτ a).unique h (hover a)
    subst this
    exact hread a

end GlobalTheory.HTW.Rec
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ProdReorder


noncomputable section

open scoped TensorProduct

namespace GlobalTheory.ProdReorder

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ind₂_line_left {r : ℕ} (h : 0 + r = r) {M V : Type} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin 0) k) M) (κ : M ≃ₗ[ℂ] ℂ)
    (π : Representation ℂ (GL (Fin r) k) V) (hπ : IsSmooth π) :
    Nonempty ((ind₂ (stdSum h) (extTensor σ π)).Equiv π) := by
  haveI : Subsingleton (GL (Fin 0) k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  have hE : ∀ g w, σ g w = w := fun g w => by rw [Subsingleton.elim g 1, map_one]; rfl
  let L : V ≃ₗ[ℂ] M ⊗[ℂ] V :=
    (TensorProduct.lid ℂ V).symm ≪≫ₗ TensorProduct.congr κ.symm (LinearEquiv.refl ℂ V)
  let u := κ.symm 1
  have hL : ∀ v, L v = u ⊗ₜ[ℂ] v := fun v => by simp [L, u]
  have hs : ∀ i : Fin r, stdSum h (Sum.inr i) = i := fun i => Fin.ext (by simp)
  have hl : ∀ p : parab k (two (stdSum h)), (leviProj k (two (stdSum h)) p true : GL (Fin r) k) = p :=
    fun p => by
      ext i j
      rw [leviProj_apply, two_true, two_true, hs, hs]
  have hd : ∀ p : parab k (two (stdSum h)),
      deltaHalf k (Two (Fin 0) (Fin r)) (leviProj k (two (stdSum h)) p) = 1 := fun p => by
    have : leviProj k (two (stdSum h)) p =
        leviTwo k _ _ ((leviTwo k (Fin 0) (Fin r)).symm (leviProj k (two (stdSum h)) p)) :=
      ((leviTwo k _ _).apply_symm_apply _).symm
    rw [this, deltaHalf_two,
      Subsingleton.elim ((leviTwo k (Fin 0) (Fin r)).symm (leviProj k (two (stdSum h)) p)).1 1]
    simp
  have hP : ∀ g : GL (Fin r) k, g ∈ parab k (two (stdSum h)) := fun g =>
    (mem_parab_two k).2 fun j i => i.elim0
  have law : ∀ (p : parab k (two (stdSum h))) v,
      (deltaHalf k (Two (Fin 0) (Fin r)) (leviProj k (two (stdSum h)) p) : ℂ) •
        (extTensor σ π) ((leviTwo k (Fin 0) (Fin r)).symm (leviProj k (two (stdSum h)) p)) (L v) =
          L (π p v) := fun p v => by
    rw [hd, Units.val_one, one_smul, hL, hL, extTensor_tmul, hE]
    congr 1
    exact congrArg (fun g => π g v) (hl p)
  let f : π.IntertwiningMap (ind₂ (stdSum h) (extTensor σ π)) :=
    { toFun := fun v => ⟨⟨fun x => L (π x v), fun p x => by
          show L (π (↑p * x) v) = (deltaHalf k _ (leviProj k _ p) : ℂ) •
            (extTensor σ π) ((leviTwo k (Fin 0) (Fin r)).symm (leviProj k _ p)) (L (π x v))
          rw [law, map_mul, Module.End.mul_apply]⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hπ v).mem_nhds (by simp)) fun g hg => by
          have hg' : π g v = v := hg
          refine Subtype.ext (funext fun x => ?_)
          show L (π (x * g) v) = L (π x v)
          rw [map_mul, Module.End.mul_apply, hg'])⟩
      map_add' := fun v w => Subtype.ext (Subtype.ext (funext fun x => by
        show L (π x (v + w)) = L (π x v) + L (π x w)
        rw [map_add (f := _), map_add (f := _)]))
      map_smul' := fun c v => Subtype.ext (Subtype.ext (funext fun x => by
        show L (π x ((c : ℂ) • v)) = (c : ℂ) • L (π x v)
        rw [map_smul, map_smul]))
      isIntertwining' := fun g => LinearMap.ext fun v => Subtype.ext (Subtype.ext (funext fun x => by
        show L (π x (π g v)) = L (π (x * g) v)
        rw [map_mul, Module.End.mul_apply])) }
  have hb : Function.Bijective f := by
    refine ⟨fun v w hvw => ?_, fun φ => ⟨L.symm (φ.1.1 1), ?_⟩⟩
    · have h1 : L (π 1 v) = L (π 1 w) := congrArg (fun φ => φ.1.1 1) hvw
      rw [map_one, Module.End.one_apply, Module.End.one_apply] at h1
      exact L.injective h1
    · refine Subtype.ext (Subtype.ext (funext fun x => ?_))
      have h1 := φ.1.2 ⟨x, hP x⟩ 1
      rw [mul_one] at h1
      refine (law ⟨x, hP x⟩ _).symm.trans ?_
      rw [L.apply_symm_apply]
      exact h1.symm
  exact ⟨(GlobalTheory.LocGL.equivOfBijective f hb).symm⟩


variable (k) in
theorem ind₂_unit_left (r t : ℕ) (h : t + r = r) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin r) k) V) (hπ : IsSmooth π) (d : Fin 0 → ℕ) (X : Fin 0 → Type)
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (τ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a))
    (e : (Σ a, Fin (d a)) ≃ Fin t) :
    Nonempty ((ind₂ (stdSum h) (extTensor (multiProd e τ) π)).Equiv π) := by
  have ht : t = 0 := by omega
  subst ht
  haveI : Subsingleton (GL (Fin 0) k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  let ev1 : IndSp e (piTensor τ) →ₗ[ℂ] ⨂[ℂ] i, X i :=
    { toFun := fun f => f.1.1 1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let κ : IndSp e (piTensor τ) ≃ₗ[ℂ] ℂ := (LinearEquiv.ofBijective ev1 ⟨fun f g hfg =>
    Subtype.ext (Subtype.ext (funext fun x => by rw [Subsingleton.elim x 1]; exact hfg)), fun v =>
    ⟨⟨⟨fun _ => v, fun p _ => by rw [Subsingleton.elim p 1, map_one]; rfl⟩,
      GlobalTheory.SmGL.MultiIrr.mem_smooth_of_eventually _ (.of_forall fun _ _ => rfl)⟩, rfl⟩⟩).trans
    (PiTensorProduct.isEmptyEquiv _)
  exact ind₂_line_left h (multiProd e τ) κ π hπ

end GlobalTheory.ProdReorder
end
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

noncomputable section

namespace GlobalTheory.TameIwahori

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isSmoothChar_of_eq_on_units {ψ θ : kˣ →* ℂˣ} (hθ : IsSmoothChar θ)
    (h : ∀ u : kˣ, valuation k (u : k) = 1 → ψ u = θ u) : IsSmoothChar ψ := by
  have h1 : IsUnram (ψ * θ⁻¹) := fun u hu => by simp [h u hu]
  have h2 : ψ = (ψ * θ⁻¹) * θ := by ext u; simp
  rw [h2]
  exact (isSmoothChar_of_isUnram h1).mul hθ

theorem exists_prinSeries (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    (hD : GlobalTheory.Published.DepthZeroJacquetInjective) {n : ℕ} (π : Irr k n) {v : π.V} {θ : Fin n → kˣ →* ℂˣ}
    (hθ : ∀ i, IsSmoothChar (θ i)) (hv : v ≠ 0) (h : IsIwVec θ π.π v) :
    ∃ ψ : Fin n → kˣ →* ℂˣ, (∀ i (u : kˣ), valuation k (u : k) = 1 → ψ i u = θ i u) ∧
      (∀ i, InSupport π.π (ψ i)) ∧ IsSubquotient π.π (prinSeries ψ) := by
  have hl : HasFiniteLength (jacB π.π) :=
    (hasFiniteLength_comp_iff _ _ (leviTorus k (Fin n)).surjective).2
      ((hBZ k).2.1 _ _ _ (points (Fin n)) _ π.π π.smooth (hasFiniteLength_of_isIrreducible π.irr))
  obtain ⟨ψ, l, hl0, hψ, hu⟩ := GlobalTheory.T.exists_torusEigenform_of_compactTorus_eigenvector k n _ (jacB π.π) (Submodule.Quotient.mk v) θ
    (isSmooth_jacB π.smooth) hl hθ (GlobalTheory.T.tameIwahoriEigenvector_jacquetQuotient_ne_zero hD k n π v θ hv h) fun t ht => by
      rw [UnramFixed.jacB_apply, jacBU_mk, h.2 t ht]
      have : ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom) t = 1 :=
        UnramFixed.deltaHalf_torusO k ht
      rw [this]
      simp
  exact ⟨ψ, hu, GlobalTheory.T.mem_supercuspidalSupport_of_torus_jacquet_eigenform k n _ π.π ψ l hl0 hψ,
    SatakeExists.isSubquotient_of_eigenform π.smooth π.irr _ l hl0 hψ⟩

theorem hasFiniteLength_prinSeries (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {n : ℕ}
    {ψ : Fin n → kˣ →* ℂˣ} (hψ : ∀ i, IsSmoothChar (ψ i)) : HasFiniteLength (prinSeries ψ) := by
  have hs : IsSmoothChar (_root_.GlobalTheory.SmGL.torusChar ψ) := by
    unfold _root_.GlobalTheory.SmGL.torusChar
    refine Finset.prod_induction _ IsSmoothChar (fun _ _ => IsSmoothChar.mul) isSmoothChar_one fun a _ => ?_
    exact (hψ a).comp _ (continuous_apply a)
  refine (hBZ k).2.2.1 _ _ _ (points (Fin n)) _ _ ?_ ?_
  · refine isSmooth_comp ((isSmooth_ofChar_iff _).2 hs) _ (continuous_pi fun i => ?_)
    exact continuous_glDet.comp (continuous_apply i)
  · exact (hasFiniteLength_comp_iff _ _ (leviTorus k (Fin n)).symm.surjective).2
      (hasFiniteLength_of_isIrreducible (isIrreducible_ofChar _))

theorem exists_model (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) {n : ℕ}
    {ψ : Fin n → kˣ →* ℂˣ} (hψ : ∀ i, IsSmoothChar (ψ i)) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (A : Representation ℂ (GL (Fin n) k) V),
      Nonempty (A.Equiv (prinSeries ψ)) ∧ IsSmooth A ∧ HasFiniteLength A :=
  ⟨_, _, _, prinSeries ψ, ⟨.refl _⟩, isSmooth_parInd _ _, hasFiniteLength_prinSeries hBZ hψ⟩

theorem isCuspSupport_of_prinSeries {n : ℕ} (σ : Irr k n) {ψ : Fin n → kˣ →* ℂˣ}
    (hψ : ∀ i, IsSmoothChar (ψ i)) (h : IsSubquotient σ.π (prinSeries ψ)) :
    IsCuspSupport σ.π (fun _ : Fin n => 1) fun a => (Irr.ofDet 1 (ψ a) (hψ a)).π :=
  ⟨σ.irr, fun a => ⟨one_pos, isIrreducible_ofChar _, isCuspidal_detRep_one (hψ a)⟩, _,
    h.trans (PrinProd.isSubquotient_prinSeries_multiProd k n ψ)⟩

theorem exists_eq_of_inSupport (hG : GlobalTheory.Published.GeometricLemma) {n : ℕ} (σ : Irr k n) {ψ : Fin n → kˣ →* ℂˣ}
    (hψ : ∀ i, IsSmoothChar (ψ i)) (h : IsSubquotient σ.π (prinSeries ψ)) {μ : kˣ →* ℂˣ}
    (hμ : InSupport σ.π μ) : ∃ i, μ = ψ i := by
  have h1 := JacquetExact.inSupport_of_isSubquotient k _ _ _ _ _ μ (isSmooth_parInd _ _)
    (h.trans (PrinProd.isSubquotient_prinSeries_multiProd k n ψ)) hμ
  obtain ⟨a, ha⟩ := ProdSupport.exists_inSupport_of_multiProd hG k _ _ _ _ _ _ μ
    (fun a => (Irr.ofDet 1 (ψ a) (hψ a)).smooth) (fun a => isIrreducible_ofChar _) h1
  exact ⟨a, (Model.inSupport_one_iff _ _).1 ha⟩

def twistIrr {n : ℕ} (σ : Irr k n) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) : Irr k n where
  V := σ.V
  π := _root_.GlobalTheory.SmGL.twist σ.π (detChar (Fin n) χ)
  smooth := isSmooth_twist σ.smooth hχ.detChar
  irr := by
    have φ : Subrepresentation (_root_.GlobalTheory.SmGL.twist σ.π (detChar (Fin n) χ)) ≃o Subrepresentation σ.π :=
      { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
          have := S.toSubmodule.smul_mem (((detChar (Fin n) χ g)⁻¹ : ℂˣ) : ℂ) (S.apply_mem_toSubmodule g hv)
          rwa [_root_.GlobalTheory.SmGL.twist_apply, smul_smul, Units.inv_mul, one_smul] at this⟩
        invFun := fun S => ⟨S.toSubmodule, fun g v hv =>
          S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_rel_iff' := Iff.rfl }
    exact φ.isSimpleOrder_iff.2 σ.irr

theorem tameSplit : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemma →
    GlobalTheory.Published.UnlinkedProductIrreducible → GlobalTheory.Published.DepthZeroJacquetInjective →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], TameSplit k := by
  intro hBZ hG hU hD k _ _ _ _ r t χ π v hχ htame hram hv hpar
  let θ : Fin (r + t) → kˣ →* ℂˣ := Fin.append (fun _ : Fin r => 1) fun _ : Fin t => χ
  have hθ : ∀ i, IsSmoothChar (θ i) := fun i => by
    induction i using Fin.addCases with
    | left i => simpa [θ] using isSmoothChar_one
    | right i => simpa [θ] using hχ
  obtain ⟨ψ, hψθ, -, hsub⟩ := exists_prinSeries hBZ hD π hθ hv (GlobalTheory.T.tameIwahoriTorusCharVector_of_parahoricDetCharVector k r t χ _ π.π v htame hpar)
  have hψ : ∀ i, IsSmoothChar (ψ i) := fun i => isSmoothChar_of_eq_on_units (hθ i) (hψθ i)
  let ψ₁ : Fin r → kˣ →* ℂˣ := fun i => ψ (Fin.castAdd t i)
  let ψ₂ : Fin t → kˣ →* ℂˣ := fun i => ψ (Fin.natAdd r i)
  have hψ₁ : ∀ i (u : kˣ), valuation k (u : k) = 1 → ψ₁ i u = 1 := fun i u hu => by
    simpa [θ] using hψθ (Fin.castAdd t i) u hu
  have hψ₂ : ∀ i (u : kˣ), valuation k (u : k) = 1 → ψ₂ i u = χ u := fun i u hu => by
    simpa [θ] using hψθ (Fin.natAdd r i) u hu
  have happ : Fin.append ψ₁ ψ₂ = ψ := Fin.append_castAdd_natAdd
  rw [← happ] at hsub
  obtain ⟨σ₁, σ₂, h₁, h₂, hπ⟩ : ∃ (σ₁ : Irr k r) (σ₂ : Irr k t), IsSubquotient σ₁.π (prinSeries ψ₁) ∧
      IsSubquotient σ₂.π (prinSeries ψ₂) ∧ IsSubquotient π.π (prod₂ σ₁.π σ₂.π) := by
    obtain ⟨V, _, _, A, ⟨φA⟩, sA, lA⟩ := exists_model hBZ (ψ := ψ₁) fun i => hψ _
    obtain ⟨W, _, _, B, ⟨φB⟩, sB, lB⟩ := exists_model hBZ (ψ := ψ₂) fun i => hψ _
    obtain ⟨σ₁, σ₂, h₁, h₂, hπ⟩ := GlobalTheory.T.exists_irreducible_subquotient_twoBlockConstituents k r t _ _ _ π.π A B π.irr sA sB lA lB
      (hsub.trans (GlobalTheory.T.prinSeries_append_isSubquotient_prod₂ k r t ψ₁ ψ₂ V W A B ⟨φA⟩ ⟨φB⟩))
    exact ⟨σ₁, σ₂, h₁.trans (.of_injective φA.toIntertwiningMap φA.injective),
      h₂.trans (.of_injective φB.toIntertwiningMap φB.injective), hπ⟩
  have hirr : (prod₂ σ₁.π σ₂.π).IsIrreducible := by
    refine hU k r t r t σ₁ σ₂ _ _ _ _ (isCuspSupport_of_prinSeries σ₁ (fun i => hψ _) h₁)
      (isCuspSupport_of_prinSeries σ₂ (fun i => hψ _) h₂) ?_
    rintro a b h α ⟨φ⟩
    refine hram fun u hu => ?_
    let g : GL (Fin 1) k := Matrix.GeneralLinearGroup.scalar (Fin 1) u
    have hg : Matrix.GeneralLinearGroup.det g = u := ProdSupport.det_scalar_one rfl u
    obtain ⟨c, hc⟩ : ∃ c : ℂ, φ (1 : ℂ) = c := ⟨_, rfl⟩
    have h0 : c ≠ 0 := fun h => one_ne_zero (α := ℂ) (φ.injective ((hc.trans h).trans (map_zero φ).symm))
    have h1 : φ (detRep (Fin 1) (ψ₁ a) g (1 : ℂ)) = (detChar (Fin 1) (unrChar k α) g : ℂ) •
        detRep (Fin 1) (ψ₂ b) g c := hc ▸ φ.toIntertwiningMap.isIntertwining _ _ g (1 : ℂ)
    simp only [detRep, ofChar_apply, detChar_apply, hg, hψ₁ a u hu, hψ₂ b u hu, isUnram_unrChar k α u hu,
      Units.val_one, one_mul, one_smul] at h1
    exact Units.ext ((mul_eq_right₀ h0).1 (h1.symm.trans hc))
  obtain ⟨φ⟩ := hπ.nonempty_equiv π.irr hirr
  let f := φ.symm v
  have hf0 : f ≠ 0 := fun h => hv (φ.symm.injective (h.trans (map_zero φ.symm).symm))
  have hf : IsParahoricVec χ (prod₂ σ₁.π σ₂.π) f := fun h hh hl u hu => by
    have := φ.symm.toIntertwiningMap.isIntertwining _ _ h v
    rw [hpar h hh hl u hu, map_smul] at this
    exact this.symm
  obtain ⟨w, hw⟩ := GlobalTheory.T.parahoricVector_twoBlockProduct_exists_perm_ne_zero k r t χ _ _ σ₁.π σ₂.π f hf0 hf
  obtain ⟨s, y, hy0, hy⟩ := GlobalTheory.T.tameIwahoriVector_twoBlockProduct_perm_value_first k r t θ _ _ σ₁.π σ₂.π f w (GlobalTheory.T.tameIwahoriTorusCharVector_of_parahoricDetCharVector k r t χ _ _ f htame hf) hw
  obtain ⟨μ, hμ, hμs, -⟩ := exists_prinSeries hBZ hD σ₁ (fun i => hθ _) hy0 hy
  have hwP : GlobalTheory.Parabolic.permGL k w ∈ parab k (two (stdSum (rfl : r + t = r + t))) := by
    have key : ∀ (i : Fin r) (j : Fin t), Fin.castAdd t i ≠ w (Fin.natAdd r j) := fun i j hij => by
      obtain ⟨i, rfl⟩ := s.surjective i
      obtain ⟨a, ha⟩ := exists_eq_of_inSupport hG σ₁ (fun i => hψ _) h₁ (hμs i)
      refine hram fun u hu => ?_
      have h1 := hμ i u hu
      rw [ha, hij, Equiv.symm_apply_apply] at h1
      simpa [θ] using h1.symm.trans (hψ₁ a u hu)
    refine (mem_parab_two k).2 fun j i => (GlobalTheory.Parabolic.permGL_apply w _ _).trans (if_neg fun hji => ?_)
    have hF : ∀ b, ∃ c, w (Fin.natAdd r b) = Fin.natAdd r c := fun b => by
      generalize hx : w (Fin.natAdd r b) = x
      induction x using Fin.addCases with
      | left a => exact absurd hx.symm (key a b)
      | right c => exact ⟨c, rfl⟩
    choose c hc using hF
    have hinj : Function.Injective c := fun b b' h =>
      Fin.natAdd_injective _ _ (w.injective (by rw [hc, hc, h]))
    obtain ⟨b, hb⟩ := Finite.surjective_of_injective hinj j
    have h2 : w (Fin.natAdd r b) = w (Fin.castAdd t i) := by rw [hc, hb]; exact hji
    have h3 := congrArg Fin.val (w.injective h2)
    have := i.2
    simp at h3
    omega
  have hf1 : f.1.1 1 ≠ 0 := fun h => hw (by
    have := f.1.2 ⟨_, hwP⟩ 1
    rw [mul_one, h, map_zero] at this
    exact this)
  obtain ⟨s₁, s₂⟩ := GlobalTheory.T.spherical_factors_of_parahoricVector_twoBlockProduct k r t χ _ _ σ₁.π σ₂.π f hf hf1
  refine ⟨σ₁, twistIrr σ₂ χ⁻¹ hχ.inv, s₁, s₂, ?_⟩
  have e : _root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.SmGL.twist σ₂.π (detChar (Fin t) χ⁻¹)) (detChar (Fin t) χ) = σ₂.π := by
    ext g x
    simp [smul_smul]
  show Nonempty (π.π.Equiv (prod₂ σ₁.π (_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.SmGL.twist σ₂.π (detChar (Fin t) χ⁻¹)) (detChar (Fin t) χ))))
  rw [e]
  exact ⟨φ.symm⟩

end GlobalTheory.TameIwahori
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.acris_mem_betaAdicClosure_ainfAdjoinBeta : ∀ (l : ℕ) [Fact l.Prime] (j : Per.Acris l →+* Per.BdRp l), IsCrisP j → ∀ (ϖ : Per.Fl l),
  (∀ a : Per.Acris0 l, (a : Per.AinfP l) ∈ Sa ϖ) → (∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n}) →
  ∀ x : Per.Acris l, j x ∈ Clos (Sg ϖ) (betaD ϖ) := by
  first | exact @GlobalTheory.Pst.StLat.acris_mem_clos | exact GlobalTheory.Pst.StLat.acris_mem_clos | (intros; apply GlobalTheory.Pst.StLat.acris_mem_clos <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.filP_eq_span_betaD_pow_of_kerP_eq_span_beta : ∀ (l : ℕ) [Fact l.Prime] (Co : Core l) (ϖ : Per.Fl l), Per.kerP l = Ideal.span {beta ϖ} →
  ∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n} := by
  first | exact @GlobalTheory.Pst.StLat.filtration_eq_span_pow | exact GlobalTheory.Pst.StLat.filtration_eq_span_pow | (intros; apply GlobalTheory.Pst.StLat.filtration_eq_span_pow <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.ainfAdjoinBetaImage_div_beta_pow : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), ϖ.untilt = ((l : ℕ) : Per.OC l) → Per.kerP l = Ideal.span {beta ϖ} →
  (∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n}) →
  ∀ s ∈ Sg ϖ, ∀ i : ℕ, betaD ϖ ^ i ∣ s → ∃ s' ∈ Sg ϖ, s = betaD ϖ ^ i * s' := by
  first | exact @GlobalTheory.Pst.StLat.BetaDiv.Sg_div_betaD_pow | exact GlobalTheory.Pst.StLat.BetaDiv.Sg_div_betaD_pow | (intros; apply GlobalTheory.Pst.StLat.BetaDiv.Sg_div_betaD_pow <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.kerP_eq_span_beta_of_untilt_eq : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), ϖ.untilt = ((l : ℕ) : Per.OC l) → Per.kerP l = Ideal.span {beta ϖ} := by
  first | exact @GlobalTheory.Pst.StLat.ker_localizedTheta_eq_span_beta | exact GlobalTheory.Pst.StLat.ker_localizedTheta_eq_span_beta | (intros; apply GlobalTheory.Pst.StLat.ker_localizedTheta_eq_span_beta <;> assumption)
end
