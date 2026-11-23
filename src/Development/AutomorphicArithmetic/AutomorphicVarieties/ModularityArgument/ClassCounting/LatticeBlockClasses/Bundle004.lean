module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockValAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.MemPowEqv
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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

@[expose] public section

section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

noncomputable section

namespace UpperTheory.V.ZK.Cl.BlockValuationRep

private theorem cyc_cm {A : Type} [CommRing A] {G H : Type} [Group G] [Group H] (f : G →* H) {m : ℕ}
    {z : Ch A G (m + 1)} (hz : Cyc z) : Cyc (cm A f (m + 1) z) := by
  rw [Cyc, (sChain A).2.1, show bd A G m z = 0 from hz, map_zero]

private def piRep {k : Type} [Field k] {G : Type} [Group G] {B : Type} (U : B → Type) [∀ b, AddCommGroup (U b)]
    [∀ b, Module k (U b)] (ρ : ∀ b, G →* (U b ≃ₗ[k] U b)) : G →* ((∀ b, U b) ≃ₗ[k] ∀ b, U b) where
  toFun g := LinearEquiv.piCongrRight fun b => ρ b g
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

private def blk {k : Type} [Field k] {C : Type} [Group C] {B : Type} (U : B → Type) [∀ b, AddCommGroup (U b)]
    [∀ b, Module k (U b)] (χ : B → C →* kˣ) (b : B) : (C × ∀ b, U b ≃ₗ[k] U b) →* (U b ≃ₗ[k] U b) where
  toFun p := scal (U b) (χ b p.1) * p.2 b
  map_one' := by simp
  map_mul' p p' := by
    ext w
    simp [scal, Units.smul_def, smul_smul, mul_comm]

private theorem pi_add {k : Type} [Field k] {A : Type} [CommRing A] {m : ℕ} {θ : Fam k A (m + 1)} (hθ : IsAdd θ)
    {G : Type} [Group G] {z : Ch A G (m + 1)} (hz : Cyc z) (B : Type) [Fintype B] :
    ∀ (U : B → Type) [∀ b, AddCommGroup (U b)] [∀ b, Module k (U b)] [∀ b, Finite (U b)]
      (V : Type) [AddCommGroup V] [Module k V] [Finite V] (φ : V ≃ₗ[k] ∀ b, U b) (ρ : G →* (V ≃ₗ[k] V))
      (ρ' : ∀ b, G →* (U b ≃ₗ[k] U b)), (∀ g w b, φ (ρ g w) b = ρ' b g (φ w b)) →
        θ V (cm A ρ (m + 1) z) = ∑ b, θ (U b) (cm A (ρ' b) (m + 1) z) := by
  refine Fintype.induction_empty_option (P := fun B _ => ∀ (U : B → Type) [∀ b, AddCommGroup (U b)]
      [∀ b, Module k (U b)] [∀ b, Finite (U b)]
      (V : Type) [AddCommGroup V] [Module k V] [Finite V] (φ : V ≃ₗ[k] ∀ b, U b) (ρ : G →* (V ≃ₗ[k] V))
      (ρ' : ∀ b, G →* (U b ≃ₗ[k] U b)), (∀ g w b, φ (ρ g w) b = ρ' b g (φ w b)) →
        θ V (cm A ρ (m + 1) z) = ∑ b, θ (U b) (cm A (ρ' b) (m + 1) z)) ?_ ?_ ?_ B
  · intro α β _ e ih U _ _ _ V _ _ _ φ ρ ρ' h
    letI : Fintype α := Fintype.ofEquiv β e.symm
    rw [← e.sum_comp]
    exact ih (fun a => U (e a)) V (φ.trans (LinearEquiv.piCongrLeft k U e).symm) ρ (fun a => ρ' (e a))
      fun g w a => h g w (e a)
  · intro U _ _ _ V _ _ _ φ ρ ρ' h
    haveI : Subsingleton V := φ.toEquiv.subsingleton
    haveI : Subsingleton (V ≃ₗ[k] V) := ⟨fun a b => LinearEquiv.ext fun _ => Subsingleton.elim _ _⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact hθ.bdry V _ ((sChain A).2.2.2.2 _ m _ (cyc_cm ρ hz))
  · intro α _ ih U _ _ _ V _ _ _ φ ρ ρ' h
    let ψ : V ≃ₗ[k] (U none × ∀ a, U (some a)) := φ.trans (LinearEquiv.piOptionEquivProd k)
    have hψ : (cj ψ).comp ρ = sumRep (ρ' none) (piRep (fun a => U (some a)) fun a => ρ' (some a)) := by
      refine MonoidHom.ext fun g => LinearEquiv.ext fun y => ?_
      obtain ⟨w, rfl⟩ := ψ.surjective y
      change ψ (ρ g (ψ.symm (ψ w))) = _
      rw [ψ.symm_apply_apply]
      exact Prod.ext (h g w none) (funext fun a => h g w (some a))
    rw [Fintype.sum_option, ← hθ.iso V _ ψ _ (cyc_cm ρ hz), ← (sChain A).2.2.1, hψ, hθ.add _ _ _ _ _ _ hz,
      ih (fun a => U (some a)) _ (LinearEquiv.refl k _) _ (fun a => ρ' (some a)) fun _ _ _ => rfl]

end UpperTheory.V.ZK.Cl.BlockValuationRep

open UpperTheory.V.ZK.Cl.BlockValuationRep in
theorem UpperTheory.V.ZK.Cl.cBlockVal :
    UpperTheory.V.ZK.Cl.CBlockVal := by
  unfold UpperTheory.V.ZK.Cl.CBlockVal
  intro k _ q _ e ζ hζ v θ hθ hv B _ U _ _ _ V _ _ _ φ σ g x g' hσ hg
  obtain ⟨-, -, h2, h3, -⟩ := sChain (ZMod q)
  let χ : B → Cq q →* kˣ := fun b => chi q ζ hζ (x b)
  let R : (Cq q × ∀ b, U b ≃ₗ[k] U b) →* (V ≃ₗ[k] V) := (cj φ.symm).comp (piRep U (blk U χ))
  have hR : ∀ p w b, φ (R p w) b = blk U χ b p (φ w b) := by
    intro p w b
    simp [R, cj, piRep]
  have hRg : R (1, g') = g := by
    refine LinearEquiv.ext fun w => φ.injective (funext fun b => ?_)
    rw [hR, hg]
    simp [blk]
  have hRσ : R.comp (MonoidHom.inl _ _) = σ := by
    refine MonoidHom.ext fun c => LinearEquiv.ext fun w => φ.injective (funext fun b => ?_)
    rw [hσ, MonoidHom.comp_apply, MonoidHom.inl_apply, hR]
    simp [blk, scal, Units.smul_def, χ]
  have hblk : ∀ b, (blk U χ b).comp (MonoidHom.inl _ _) = (scal (U b)).comp (χ b) := by
    intro b
    refine MonoidHom.ext fun c => ?_
    simp [blk]
  have hk0 : ∀ b, blk U χ b (1, g') = g' b := by
    intro b
    simp [blk]
  have hy : Cyc (cm (ZMod q) (MonoidHom.inl (Cq q) (∀ b, U b ≃ₗ[k] U b)) (2 * e + 1 + 1) (zc q e)) :=
    cyc_cm _ (sZc q e)
  have hconj : (MulAut.conj ((1 : Cq q), g')⁻¹).toMonoidHom.comp (MonoidHom.inl (Cq q) (∀ b, U b ≃ₗ[k] U b)) =
      MonoidHom.inl _ _ := by
    refine MonoidHom.ext fun c => ?_
    simp
  have hZ : Cyc (prism (ZMod q) ((1 : Cq q), g') (2 * e + 1 + 1)
      (cm (ZMod q) (MonoidHom.inl (Cq q) (∀ b, U b ≃ₗ[k] U b)) (2 * e + 1 + 1) (zc q e))) := by
    show bd _ _ (2 * e + 1 + 1) _ = 0
    have s := sPrism (ZMod q) _ ((1 : Cq q), g') (2 * e + 1) (cm (ZMod q) (MonoidHom.inl (Cq q) (∀ b, U b ≃ₗ[k] U b)) (2 * e + 1 + 1) (zc q e))
    have hy' : bd (ZMod q) _ (2 * e + 1) (cm (ZMod q) (MonoidHom.inl (Cq q) (∀ b, U b ≃ₗ[k] U b)) (2 * e + 1 + 1) (zc q e)) = 0 := hy
    rw [hy', map_zero, add_zero, ← h2, hconj, sub_self] at s
    exact s
  show θ V (prism (ZMod q) g (2 * e + 1 + 1) (cm (ZMod q) σ (2 * e + 1 + 1) (zc q e))) = _
  rw [← hRg, ← hRσ, h2, ← h3]
  refine (pi_add hθ hZ B U V φ R (blk U χ) hR).trans (Finset.sum_congr rfl fun b _ => ?_)
  rw [h3, ← h2, hblk b, hk0 b]
  exact hv (U b) (x b) (g' b)

end
end

section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

private def locS {L : Type} (F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F]
    (b : 𝓞 L) : Subring F where
  carrier := {x | ∀ P : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 L) (𝓞 F) b ∉ P.asIdeal → P.valuation F x ≤ 1}
  one_mem' := fun P _ => by simp
  zero_mem' := fun P _ => by simp
  mul_mem' := fun {x y} hx hy P hP => by
    rw [map_mul]; exact mul_le_one' (hx P hP) (hy P hP)
  add_mem' := fun {x y} hx hy P hP => Valuation.map_add_le _ (hx P hP) (hy P hP)
  neg_mem' := fun {x} hx P hP => by rw [Valuation.map_neg]; exact hx P hP

private theorem exists_res {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F]
    {k : Type} [Field k] (r : 𝓞 F →+* k) (b : 𝓞 L) (hb : r (algebraMap (𝓞 L) (𝓞 F) b) ≠ 0) (σ : F ≃ₐ[L] F) :
    ∃ ρ : locS F b →+* k, ∀ x : locS F b, ResF r (σ x) (ρ x) := by
  obtain ⟨h1, h2, h3, h4⟩ := UpperTheory.V.ZK.Cl.cRes L F k r
  obtain ⟨a1, a2, a3, a4, -⟩ := UpperTheory.V.ZK.Cl.cAct L F
  have hex : ∀ x : locS F b, ∃ u, ResF r (σ x) u := by
    intro x
    refine ((h4 b hb).1 (σ x) fun P hP => ?_).2
    have e : P = actP σ (actP σ⁻¹ P) := by rw [← a2, mul_inv_cancel, a3]
    rw [e, a1]
    exact x.2 _ (by rwa [a4])
  choose f hf using hex
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hf⟩
  · refine h1 _ _ _ (hf 1) ?_
    simpa using h2 1
  · intro x y
    refine h1 _ _ _ (hf (x * y)) ?_
    simpa using (h3 _ _ _ _ (hf x) (hf y)).2
  · refine h1 _ _ _ (hf 0) ?_
    simpa using h2 0
  · intro x y
    refine h1 _ _ _ (hf (x + y)) ?_
    simpa using (h3 _ _ _ _ (hf x) (hf y)).1

private theorem exists_mat {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F]
    {I : Type} [Fintype I] [DecidableEq I] (b : 𝓞 L) (g : (I → F) →ₗ[F] (I → F))
    (hg : ∀ x, InLoc b x → InLoc b (g x)) :
    ∃ A : Matrix I I (locS F b), (locS F b).subtype.mapMatrix A = LinearMap.toMatrix' g := by
  refine ⟨fun i j => ⟨g (Pi.single j 1) i, hg _ (fun i' P _ => ?_) i⟩, ?_⟩
  · by_cases h : i' = j
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  · ext i j
    rw [LinearMap.toMatrix'_apply]
    rfl

theorem UpperTheory.V.ZK.Cl.cMat :
    UpperTheory.V.ZK.Cl.CMat := by
  intro L F _ _ _ _ _ I _ k _ r b hb g hg
  classical
  obtain ⟨A, hA⟩ := exists_mat b (g : (I → F) →ₗ[F] (I → F)) fun x hx => (hg x).1 hx
  obtain ⟨B, hB⟩ := exists_mat b (g.symm : (I → F) →ₗ[F] (I → F)) fun x hx =>
    (hg _).2 (by simpa using hx)
  have hinj : Function.Injective ((locS F b).subtype.mapMatrix : Matrix I I (locS F b) → Matrix I I F) := by
    intro X Y h
    ext i j
    exact congrFun (congrFun h i) j
  have hAB : A * B = 1 := by
    apply hinj
    rw [map_mul, hA, hB, ← LinearMap.toMatrix'_comp, map_one]
    simp
  have hBA : B * A = 1 := by
    apply hinj
    rw [map_mul, hA, hB, ← LinearMap.toMatrix'_comp, map_one]
    simp
  have hdet : ((LinearEquiv.det g : Fˣ) : F) = (A.det : locS F b) := by
    rw [LinearEquiv.coe_det, ← LinearMap.det_toMatrix', ← hA, ← RingHom.map_det]
    rfl
  refine ⟨fun P hP => ?_, fun σ => ?_⟩
  · have h1 : ((A.det : locS F b) : F) * (B.det : locS F b) = 1 := by
      rw [← Subring.coe_mul, ← Matrix.det_mul, hAB]; simp
    have h2 := congrArg (P.valuation F) h1
    rw [map_mul, map_one] at h2
    have h3 : P.valuation F ((A.det : locS F b) : F) = 1 :=
      le_antisymm (A.det.2 P hP) (h2.symm.le.trans (mul_le_of_le_one_right' (B.det.2 P hP)))
    rw [ordP, hdet, h3]; simp
  · obtain ⟨ρ, hρ⟩ := exists_res r b hb σ
    obtain ⟨h1, h2, h3, h4⟩ := UpperTheory.V.ZK.Cl.cRes L F k r
    refine ⟨Matrix.toLin'OfInv (M := ρ.mapMatrix B) (M' := ρ.mapMatrix A)
      (by rw [← map_mul, hBA, map_one]) (by rw [← map_mul, hAB, map_one]), ?_, fun w u hw hu i => ?_⟩
    · have := hρ A.det
      rw [← hdet, RingHom.map_det, ← LinearMap.det_toLin'] at this
      unfold Res
      rw [LinearEquiv.coe_det]
      exact this
    · let w' : I → locS F b := fun i => ⟨w i, hw i⟩
      have e1 : u = fun i => ρ (w' i) := funext fun i => h1 _ _ _ (hu i) (hρ (w' i))
      have e2 : g w i = (A.mulVec w' i : locS F b) := by
        have : g w = Matrix.mulVec (LinearMap.toMatrix' (g : (I → F) →ₗ[F] (I → F))) w := by
          simp
        rw [this, ← hA]
        exact (RingHom.map_mulVec (locS F b).subtype A w' i).symm
      have := hρ (A.mulVec w' i)
      rw [← e2, RingHom.map_mulVec] at this
      rw [e1]
      exact this
end

section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

theorem UpperTheory.V.ZK.Cl.cUnit :
    UpperTheory.V.ZK.Cl.CUnit := by
  intro L F _ _ _ _ _ k _ r b hb q v
  obtain ⟨_, hmul, hone, hmem, hinv, hadd, hpow⟩ := cAct L F
  have hres := (cRes L F k r).2.2.2 b hb |>.2
  have h1 : ∀ P : HeightOneSpectrum (𝓞 F), ordP P 1 = 0 := fun P => by
    simpa using hpow P 1 0
  let U : Subgroup Fˣ :=
    { carrier := {x | IsBU b x}
      mul_mem' := fun {x y} hx hy P hP => by rw [hadd, hx P hP, hy P hP, add_zero]
      one_mem' := fun P _ => h1 P
      inv_mem' := fun {x} hx P hP => by
        have := hpow P x (-1)
        rw [zpow_neg_one] at this
        rw [this, hx P hP, mul_zero] }
  have uniq : ∀ (x : Fˣ) (u u' : kˣ), Res r x u → Res r x u' → u = u' := by
    rintro x u u' ⟨a, c, hc, hxc, hac⟩ ⟨a', c', hc', hxc', hac'⟩
    have e0 : ((a * c' : 𝓞 F) : F) = ((a' * c : 𝓞 F) : F) := by
      push_cast
      linear_combination (-(c' : F)) * hxc + (c : F) * hxc'
    have e : a * c' = a' * c := by exact_mod_cast e0
    have e2 := congrArg r e
    rw [map_mul, map_mul, hac, hac'] at e2
    have : (u : k) = u' := by
      have hcc : r c * r c' ≠ 0 := mul_ne_zero hc hc'
      apply mul_right_cancel₀ hcc
      linear_combination e2
    exact Units.ext this
  classical
  let f : Fˣ → ZMod q := fun x =>
    if h : ∃ u, Res r x u then Multiplicative.toAdd (v h.choose) else 0
  have fspec : ∀ (x : Fˣ) (u : kˣ), Res r x u → f x = Multiplicative.toAdd (v u) := by
    intro x u hu
    have h : ∃ u, Res r x u := ⟨u, hu⟩
    simp only [f, dif_pos h]
    rw [uniq x _ _ h.choose_spec hu]
  have resmul : ∀ (x y : Fˣ) (u w : kˣ), Res r x u → Res r y w → Res r (x * y) (u * w) := by
    rintro x y u w ⟨a, c, hc, hxc, hac⟩ ⟨a', c', hc', hxc', hac'⟩
    refine ⟨a * a', c * c', by rw [map_mul]; exact mul_ne_zero hc hc', ?_, ?_⟩
    · push_cast
      linear_combination (y * (c' : F)) * hxc + (a : F) * hxc'
    · rw [map_mul, map_mul, hac, hac', Units.val_mul]
      ring
  refine ⟨U, f, fun x => Iff.rfl, ?_, ?_, ?_, fspec, fun x hx => hres x hx⟩
  · intro σ x hx P hP
    have hQ : actP σ (actP σ⁻¹ P) = P := by rw [← hmul, mul_inv_cancel, hone]
    have hb' : (algebraMap (𝓞 L) (𝓞 F)) b ∉ (actP σ⁻¹ P).asIdeal := by
      rw [← hmem σ (actP σ⁻¹ P) b, hQ]
      exact hP
    have := hinv σ (actP σ⁻¹ P) x
    rw [hQ] at this
    rw [this]
    exact hx _ hb'
  · intro x hx y hy
    obtain ⟨u, hu⟩ := hres x hx
    obtain ⟨w, hw⟩ := hres y hy
    rw [fspec _ _ (resmul x y u w hu hw), fspec _ _ hu, fspec _ _ hw, map_mul, toAdd_mul]
  · have h11 : Res r 1 1 := ⟨1, 1, by simp, by simp, by simp⟩
    rw [fspec _ _ h11, map_one, toAdd_one]
end

section

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl Polynomial

private theorem shift_sum (p : ℤ[X]) (a : ℤ) (d : ℕ → ℤ) :
    ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (d (i + 1) - a * d i) =
      ∑ i ∈ Finset.range (p.natDegree + 1 + 1), (p * (X - C a)).coeff i * d i := by
  have hmul : ∀ i, (p * (X - C a)).coeff i = (p * X).coeff i - a * p.coeff i := by
    intro i
    rw [mul_sub, coeff_sub, coeff_mul_C, mul_comm a]
  have h1 : ∑ i ∈ Finset.range (p.natDegree + 1 + 1), (p * X).coeff i * d i =
      ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * d (i + 1) := by
    rw [Finset.sum_range_succ']
    simp [coeff_mul_X]
  have h2 : ∑ i ∈ Finset.range (p.natDegree + 1 + 1), a * p.coeff i * d i =
      ∑ i ∈ Finset.range (p.natDegree + 1), a * p.coeff i * d i := by
    rw [Finset.sum_range_succ, coeff_eq_zero_of_natDegree_lt (by omega)]
    simp
  simp_rw [hmul, sub_mul, Finset.sum_sub_distrib, h1, h2, mul_sub, Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

private theorem natDegree_polE (κ : ℤ) (M E : ℕ) (h : E < M) : (polE κ M E).natDegree + 1 = M := by
  have hmem : E ∈ Finset.range M := Finset.mem_range.2 h
  unfold polE
  rw [natDegree_prod_of_monic _ _ (fun j _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
  rw [Finset.card_erase_of_mem hmem, Finset.card_range]
  omega

theorem UpperTheory.V.ZK.Cl.cBetaDiv :
    UpperTheory.V.ZK.Cl.CBetaDiv := by
  intro L F _ _ _ _ _ γ κ M E hE α 𝔡 hD P
  obtain ⟨_, hmul, hone, _, hinv, hadd, hpow⟩ := cAct L F
  have hprod : ∀ (s : Finset ℕ) (f : ℕ → Fˣ), ordP P (∏ i ∈ s, f i) = ∑ i ∈ s, ordP P (f i) := by
    intro s f
    refine Finset.induction_on s ?_ ?_
    · simpa using hpow P 1 0
    · intro j s hj ih
      rw [Finset.prod_insert hj, Finset.sum_insert hj, hadd, ih]
  have key : ∀ i : ℕ, ordP P (actU (γ⁻¹ ^ i) α) =
      𝔡 (actP (γ ^ (i + 1)) P) - (κ : ℤ) ^ E * 𝔡 (actP (γ ^ i) P) := by
    intro i
    have hP : actP (γ⁻¹ ^ i) (actP (γ ^ i) P) = P := by
      rw [← hmul, inv_pow, inv_mul_cancel, hone]
    have h0 := hinv (γ⁻¹ ^ i) (actP (γ ^ i) P) α
    rw [hP] at h0
    rw [h0, hD, ← hmul, pow_succ']
    push_cast
    rfl
  have hpol : polE (κ : ℤ) M E * (X - C ((κ : ℤ) ^ E)) = pol (κ : ℤ) M := by
    rw [mul_comm]
    exact Finset.mul_prod_erase (Finset.range M) (fun j => X - C ((κ : ℤ) ^ j)) (Finset.mem_range.2 hE)
  have hs := shift_sum (polE (κ : ℤ) M E) ((κ : ℤ) ^ E) (fun i => 𝔡 (actP (γ ^ i) P))
  rw [hpol, natDegree_polE κ M E hE] at hs
  unfold polAct
  rw [hprod]
  simp only [hpow, key]
  rw [natDegree_polE κ M E hE] at *
  exact hs
end
