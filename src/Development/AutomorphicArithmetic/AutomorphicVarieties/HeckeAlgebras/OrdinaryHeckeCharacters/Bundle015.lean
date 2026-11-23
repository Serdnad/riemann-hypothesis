module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle037
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle086
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CoreUniq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PlaceBetween
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.GlBridge
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.NtExpand
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle043
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


private theorem w_under {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)

private theorem l_not_mem_base_prime {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) : ((l : ℕ) : 𝓞 (Lp L)) ∉ s.v0.asIdeal := by
  intro h
  have h1 : ((s.p : ℕ) : 𝓞 (Lp L)) ∈ s.v0.asIdeal := by
    rw [← s.norm_v0_eq_one]
    simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using
      Ideal.absNorm_mem s.v0.asIdeal
  have hc : IsCoprime (s.p : 𝓞 (Lp L)) (l : 𝓞 (Lp L)) :=
    ((Nat.coprime_primes s.p_prime Fact.out).2 s.p_ne).cast
  obtain ⟨a, b, hab⟩ := hc
  exact s.v0.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h)))

private theorem sum_one {M : Type} [AddCommGroup M] [Module ℂ M] {m : ℕ} {H : Type} [Group H] (τ : H →* GL (Fin m) ℂ)
    (f : Fin m → M) (i : Fin m) : ∑ j : Fin m, τ 1 i j • f j = f i := by
  simp [Matrix.one_apply]

theorem UpperTheory.V.Hi.partUR2V0 :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    YOf Q ι τ₀ e ξ σ ≠ ⊥ → ∀ τ : SmIrr (GLw n (s.w s.v0)), IsCompAlong σ (locU n (s.w s.v0)) ((cLoc (s.w s.v0)).comp (locU n (s.w s.v0)).subtype) τ.ρ → fixd τ.ρ (Kc _ n 1) ≠ ⊥ := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c ι m τ₀ lam d e ξ hξ σ hσ hY τ hτ
  have hw0 := w_under s s.v0
  have hsp : IsSplitAt (s.w s.v0) := UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA s.v0) (s.split _ (Or.inr (Or.inr rfl))) _ hw0
  obtain ⟨j, hj1, hj2, -, hj3⟩ := (UpperTheory.V.Hi.secU l L Ω s n hn _ hsp).1
  have hiso := UpperTheory.isoSum_restriction_of_local_component_unitary L n σ hσ _ j hj1 hj2 hj3 τ hτ
  obtain ⟨h1, -, -, h4⟩ := UpperTheory.V.Hi.partUR2Abs L n _ _ _ _ τ hiso
  refine h1 _ (h4 1) ?_
  obtain ⟨F, hF, hF0⟩ := (Submodule.ne_bot_iff _).1 hY
  obtain ⟨hB, hM⟩ := (UpperTheory.V.Hi.partUR2Mem l L Ω s n hn V Q c ι m τ₀ lam d e ξ σ F).1 hF
  have hinj := (UpperTheory.V.Hi.formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ _ fun _ => rfl).1
  intro hbot
  refine hF0 (funext fun i => hinj (F i) (And.left hB i (Set.mem_univ i)) fun ℓ => ?_)
  refine (Submodule.eq_bot_iff _).1 hbot _ (Submodule.mem_inf.2 ⟨hM i ℓ, fun g hg => ?_⟩)
  have hloc : ∀ u : Plc L, u.under (𝓞 (Lp L)) ≠ s.v0 → cLoc u (j g) = 1 := fun u hu =>
    MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 (hj1 g)).2 u) (hw0.symm ▸ hu))
  have h := UpperTheory.V.Hi.partUR2Fix l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ F hB (j g) (Subgroup.mem_inf.1 (hj1 g)).1
    (fun v => hloc _ fun h => l_not_mem_base_prime s (by
      rw [← h, w_under]
      exact v.2)) 1
    (fun u => (hloc _ fun h => s.v0_St (by
      rw [← h, w_under]
      exact u.2)).symm)
    ((hj2 g).symm ▸ hg)
    (fun w hw => by
      rw [hloc w fun h => hw (V.sub (Or.inr (Or.inr h)))]
      exact one_mem _)
    (fun q => hloc _ fun h => Q.notS q (Or.inr (Or.inr h))) i ℓ
  exact (sum_one _ (fun j' => RU L n (j g) (toForm ι e (F j') ℓ)) i).symm.trans h
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem UpperTheory.V.Hi.levelUR2LevOut :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (K : (hset Q τ₀).Lev) (u : Ub n s), u ∈ (hset Q τ₀).lev K → (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → cmp n w (u : Ga l L n) ∈ KO (w.adicCompletion L) (Fin n)) ∧ ∀ q : Q.Q, cmp n (Q.wq q) (u : Ga l L n) ∈ K.1 q := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c m τ₀ K u hu
  classical
  have hS : ∀ q : Q.Q, (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := fun q => by
    rw [Q.range]
    exact Or.inr ⟨q, rfl⟩
  have hsec := fun q : Q.Q => (secU l L Ω s n hn (Q.wq q)
    (UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA _) (V.split _ (hS q)) _ rfl)).2 (Q.notS q)
  have h1 : ∀ (q : Q.Q) (g : GLw n (Q.wq q)) (w : Plc L), w.under (𝓞 (Lp L)) ≠ (Q.wq q).under (𝓞 (Lp L)) →
      CaseU.cmp n w ((sec n s (Q.wq q) g : Ub n s) : Ga l L n) = 1 := fun q g w hw =>
    MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 ((hsec q).2.2 g) w) hw)
  let P : Subgroup (Ub n s) :=
    (⨅ (w : Plc L) (_ : w.under (𝓞 (Lp L)) ∉ V.S'),
      (KO (w.adicCompletion L) (Fin n)).comap ((CaseU.cmp n w).comp (Ub n s).subtype)) ⊓
    ⨅ q : Q.Q, Subgroup.comap ((CaseU.cmp n (Q.wq q)).comp (Ub n s).subtype) (K.1 q)
  have hP : ∀ x : Ub n s, x ∈ P ↔
      (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → CaseU.cmp n w (x : Ga l L n) ∈ KO (w.adicCompletion L) (Fin n)) ∧
        ∀ q : Q.Q, CaseU.cmp n (Q.wq q) (x : Ga l L n) ∈ K.1 q := fun x =>
    ⟨fun h => ⟨fun w hw => Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 h).1 w) hw,
      fun q => Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 h).2 q⟩,
     fun h => Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun hw => h.1 w hw,
      Subgroup.mem_iInf.2 fun q => h.2 q⟩⟩
  have hle : (hset Q τ₀).lev K ≤ P := by
    refine sup_le (fun x hx => ?_) (iSup_le fun q => ?_)
    · have hx' : x ∈ UQ n Q := hx
      refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx').1, Subgroup.mem_iInf.2 fun q => ?_⟩
      have e := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx').2 q)
      exact Subgroup.mem_comap.2 (e ▸ one_mem _)
    · rintro _ ⟨g, hg, rfl⟩
      refine (hP (sec n s (Q.wq q) g)).2 ⟨fun w hw => ?_, fun q' => ?_⟩
      · rw [h1 q g w fun h => hw (h ▸ hS q)]
        exact one_mem _
      · by_cases h : q' = q
        · subst h
          exact Set.mem_of_eq_of_mem ((hsec q').2.1 g) hg
        · rw [h1 q g _ fun h' => h (Q.inj h')]
          exact one_mem _
  exact (hP u).1 (hle hu)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


private theorem lc_adic {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [Alg.IsCO O R]
    [CommRing R'] [Algebra O R'] [Alg.IsCO O R'] (f : R →ₐ[O] R') {Γ : Type} [TopologicalSpace Γ] {a : Γ → R}
    (ha : Alg.AdicCont (maximalIdeal R) a) : Alg.AdicCont (maximalIdeal R') fun g => f (a g) := fun N => by
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap (f : R →+* R') := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    show f y ∈ maximalIdeal R'
    rw [← Alg.res_eq_zero_iff O, Alg.res_map, Alg.res_eq_zero_iff]
    exact hy
  exact (ha N).comp (Ideal.quotientMap _ (f : R →+* R') hle)

private theorem lc_chi {n : ℕ} {R R' G : Type} [CommRing R] [CommRing R'] [Group G] (D : W.GDet n R G) (f : R →+* R') (g : G) :
    (D.map f).chi (MonoidAlgebra.single g 1) = (D.chi (MonoidAlgebra.single g 1)).map f ∧
      ∀ i, (D.map f).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1)) := by
  have h := (CA.d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)
  rwa [MonoidAlgebra.mapRingHom_single, map_one] at h

private theorem lc_pol {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (n q : ℕ) (a : ℕ → A) :
    (Hi.heckePol n q a).map f = Hi.heckePol n q fun j => f (a j) := by

  simp [Hi.heckePol, Polynomial.map_sum]

section
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) {T' T : Type} [CommRing T'] [CommRing T] [Algebra c.O T'] [Algebra c.O T]
    (Φ : T' →ₐ[c.O] T) (v : H.V) (g : Dec (F := L) (H.pl v))

private theorem lc_eps (p : T'ˣ) (i : ℕ) :
    (Units.map Φ.toRingHom.toMonoidHom p * H.epsV T v g ^ i : Tˣ) = Units.map Φ.toRingHom.toMonoidHom (p * H.epsV T' v g ^ i) := by
  rw [map_mul, map_pow]
  congr 2
  exact Units.ext (Φ.commutes _).symm

private theorem lc_unit (p : Dec (F := L) (H.pl v) →* T'ˣ) (i : ℕ) (b' : T') (b : T) (hb : Φ b' = b)
    (h : (p g * H.epsV T' v g ^ i : T'ˣ) * b' = 1) : (W.pushCh Φ.toRingHom p g * H.epsV T v g ^ i : Tˣ) * b = 1 := by
  have e := congrArg Φ h
  rw [map_mul, map_one, hb] at e
  rw [← e]
  exact congrArg (fun u : Tˣ => (u : T) * b) (lc_eps H Φ v g (p g) i)

private theorem lc_unif (p : Fin n → Dec (F := L) (H.pl v) →* T'ˣ) (j : Fin n) (b' : T') (b : T) (hb : Φ b' = b)
    (h : ((∏ i with i ≤ j, p i g * H.epsV T' v g ^ (i : ℕ) : T'ˣ) : T') = b') :
    ((∏ i with i ≤ j, W.pushCh Φ.toRingHom (p i) g * H.epsV T v g ^ (i : ℕ) : Tˣ) : T) = b := by
  rw [← hb, ← h]
  have e : (∏ i with i ≤ j, W.pushCh Φ.toRingHom (p i) g * H.epsV T v g ^ (i : ℕ) : Tˣ) =
      Units.map Φ.toRingHom.toMonoidHom (∏ i with i ≤ j, p i g * H.epsV T' v g ^ (i : ℕ)) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ => lc_eps H Φ v g (p i g) i
  rw [e]
  rfl

end

private theorem lc_cont {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [Alg.IsCO O R]
    [CommRing R'] [Algebra O R'] [Alg.IsCO O R'] (f : R →ₐ[O] R') {n : ℕ} {G : Type} [Group G] [TopologicalSpace G]
    (D : W.GDet n R G) (h : D.IsCont (maximalIdeal R)) : (D.map f.toRingHom).IsCont (maximalIdeal R') := fun i => by
  rw [funext fun g => (lc_chi D f.toRingHom g).2 i]
  exact lc_adic f (h i)

private theorem lc_pcont {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [Alg.IsCO O R]
    [CommRing R'] [Algebra O R'] [Alg.IsCO O R'] (f : R →ₐ[O] R') {G : Type} [Group G] [TopologicalSpace G]
    (p : G →* Rˣ) (h : Alg.AdicCont (maximalIdeal R) fun g => (p g : R)) :
    Alg.AdicCont (maximalIdeal R') fun g => (W.pushCh f.toRingHom p g : R') :=
  lc_adic f h

private theorem lc_frob {O : Type} [CommRing O] {R R' : Type} [CommRing R] [Algebra O R]
    [CommRing R'] [Algebra O R'] (f : R →ₐ[O] R') {n : ℕ} {G : Type} [Group G]
    (D : W.GDet n R G) (g : G) (q : ℕ) (P : ℕ → Prop) [DecidablePred P] (b : ∀ j, P j → R) (b' : ∀ j, P j → R')
    (hb : ∀ j h, f (b j h) = b' j h)
    (h : D.chi (MonoidAlgebra.single g 1) = Hi.heckePol n q fun j => if h : P j then b j h else 1) :
    (D.map f.toRingHom).chi (MonoidAlgebra.single g 1) = Hi.heckePol n q fun j => if h : P j then b' j h else 1 := by
  rw [(lc_chi D f.toRingHom _).1, h, lc_pol]
  refine congrArg _ (funext fun j => ?_)
  split_ifs
  · exact hb _ _
  · exact map_one _

private theorem lc_comp {O : Type} [CommRing O] {R T' T : Type} [CommRing R] [Algebra O R] [CommRing T'] [Algebra O T']
    [CommRing T] [Algebra O T] (f' : R →ₐ[O] T') (Φ : T' →ₐ[O] T) (f : R →ₐ[O] T) {n : ℕ} {G V : Type} {Γ : V → Type} [Group G]
    [∀ v, Group (Γ v)] (D : W.GDet n R G) (ψ : ∀ v, Fin n → Γ v →* Rˣ)
    (hu : ∀ f g : R →ₐ[O] T, D.map f.toRingHom = D.map g.toRingHom →
      (∀ v i, W.pushCh f.toRingHom (ψ v i) = W.pushCh g.toRingHom (ψ v i)) → f = g)
    (h : D.map f.toRingHom = (D.map f'.toRingHom).map Φ.toRingHom ∧
      (fun v i => W.pushCh f.toRingHom (ψ v i)) = fun v i => W.pushCh Φ.toRingHom (W.pushCh f'.toRingHom (ψ v i))) (t : R) :
    f t = Φ (f' t) := by
  rw [hu f (Φ.comp f') (h.1.trans ((CA.d_gmap D).2.1 _ _)) fun v i => congrFun (congrFun h.2 v) i]
  rfl


private theorem lc_univ {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A] [IsLocalRing A] (θ : H.X.I.T →* Aˣ)
    (a : H.Op → c.O) (K K' : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)]
    [Fact (CommOn (H.MK θ a K') (H.op A))] [Alg.IsCO c.O (H.TK θ a K')] (Φ : H.TK θ a K' →ₐ[c.O] H.TK θ a K)
    (hΦg : ∀ i, Φ (H.gen θ a K' i) = H.gen θ a K i) (hΦA : ∀ b, Φ (algebraMap A _ b) = algebraMap A _ b)
    (D : W.GDet n (H.TK θ a K') H.Gq) (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K')ˣ)
    (hU : H.IsUniv θ a K' (maximalIdeal _) D ψ) :
    H.IsUniv θ a K (maximalIdeal _) (D.map Φ.toRingHom) fun v i => W.pushCh Φ.toRingHom (ψ v i) := by
  refine { cont := lc_cont Φ D hU.cont, ψ_cont := ?_, frob := ?_, ψ_unit := ?_, ψ_unif := ?_ }
  · intro v i
    exact lc_pcont Φ (ψ v i) (hU.ψ_cont v i)
  · intro w B σ hB hσ
    exact lc_frob Φ D _ _ (fun j => 0 < j ∧ j - 1 < n) _ _ (fun _ _ => hΦg _) (hU.frob w B σ hB hσ)
  · intro v i s g u hg hs
    exact lc_unit H Φ v g (ψ v i) i _ _ (hΦA _) (hU.ψ_unit v i s g u hg hs)
  · intro v j s g hg hs
    exact lc_unif H Φ v g (ψ v) j _ _ (hΦg _) (hU.ψ_unif v j s g hg hs)


theorem UpperTheory.V.Hi.levelUR2Compat :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (a : H.Op → c.O) (K K' : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)] [Fact (CommOn (H.MK θ a K') (H.op A))] [Alg.IsCO c.O (H.TK θ a K')] (R : Type) [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R H.Gq) (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ), (∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (f g : R →ₐ[c.O] T), D₀.map f.toRingHom = D₀.map g.toRingHom → (∀ v i, W.pushCh f.toRingHom (ψ₀ v i) = W.pushCh g.toRingHom (ψ₀ v i)) → f = g) → ∀ (f : R →ₐ[c.O] H.TK θ a K) (f' : R →ₐ[c.O] H.TK θ a K'), H.IsMap θ a K D₀ ψ₀ f → H.IsMap θ a K' D₀ ψ₀ f' → ∀ φ : H.MK θ a K →ₗ[A] H.MK θ a K', Function.Injective φ → (∀ i (y : H.MK θ a K), ((φ ((H.gen θ a K i : Module.End A (H.MK θ a K)) y) : H.MK θ a K') : H.X.Fn A H.m) = H.op A i (φ y)) → ∀ t y, φ ((f t : Module.End A (H.MK θ a K)) y) = (f' t : Module.End A (H.MK θ a K')) (φ y) := by
  intro hN L Ω _ _ _ _ _ l _ n c H hA A _ _ _ θ hθ a K K' _ _ _ _ R _ _ D₀ ψ₀ huniq f f' hf hf' φ hφ hgen t y
  obtain ⟨Ψ, hΨg, hΨ⟩ := levelUR2HeckeMap A _ _ _ _ (H.MK θ a K) (H.MK θ a K') (H.op A) (H.op A) φ id hφ hgen
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : H.TK θ a K' →ₐ[c.O] H.TK θ a K, ∀ x, Φ x = Ψ x := ⟨Ψ.restrictScalars c.O, fun _ => rfl⟩
  have hM := lc_univ H θ a K K' Φ (fun i => (hΦ _).trans (hΨg i)) (fun b => (hΦ _).trans (Ψ.commutes b)) _ _ hf'
  have e := lc_comp f' Φ f D₀ ψ₀ (huniq _) (coreUniq hN L Ω l n c H hA A θ hθ a K _ _ hM _ _ hf) t
  rw [e, hΦ]
  exact hΨ (f' t) y
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

section SlopeTestRemainingChoices

private theorem th_Uc {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (W : Subgroup kˣ) (hW : IsOpen (W : Set kˣ)) : ∃ c, ∀ d, c ≤ d → Uc k d ≤ W := by
  obtain ⟨c, hc⟩ := (glBridge k 1 ℂ 1).2.2.2.1 (W.comap Matrix.GeneralLinearGroup.det)
    (hW.preimage Matrix.GeneralLinearGroup.continuous_det)
  refine ⟨c, fun d hd => ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  have h1 : (u : 𝒪[k]) - 1 ∈ maximalIdeal 𝒪[k] ^ c :=
    Ideal.pow_le_pow_right hd (Ideal.Quotient.eq.1 (congrArg Units.val hu))
  have h2 := hc (x := Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) (diagT 𝒪[k] (Fin 1) fun _ => u))
    ⟨_, by
      ext i j
      rw [Subsingleton.elim j i]
      simpa [val_diagT] using Ideal.Quotient.eq.2 h1, rfl⟩
  convert Subgroup.mem_comap.1 h2 using 1
  ext
  simp [val_diagT]

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {A : ValuationSubring Ω} {w : Plc F} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion F)ˣ}

private theorem th_fin (ha : IsLocalArtin h a) {B : Type} [CommGroup B] [Finite B] (f : Weil h →* B)
    (hf : GlobalTheory.WeilDeligne.IsSmooth f) : ∃ c, ∀ d, c ≤ d → ∀ σ, a σ ∈ Uc _ d → f σ = 1 := by
  choose φ hφ using fun b : {b : B // b ≠ 1} => CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity B ℂ b.2
  choose χ hχ e using fun b => ha.factor ((φ b).comp f) (hf.of_le fun σ hσ => by simp [hσ])
  obtain ⟨c, hc⟩ := th_Uc (⨅ b, (χ b).ker) (by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite hχ)
  refine ⟨c, fun d hd σ hσ => by_contra fun h1 => hφ ⟨_, h1⟩ ?_⟩
  exact (DFunLike.congr_fun (e ⟨_, h1⟩) σ).trans (Subgroup.mem_iInf.1 (hc d hd hσ) _)

private theorem th_char (ha : IsLocalArtin h a) {R : Type} [CommRing R] [IsCNL R] (ψ : Dec (F := F) A →* Rˣ)
    (hψ : Alg.AdicCont (maximalIdeal R) fun g => (ψ g : R)) :
    ∃ χ : (w.adicCompletion F)ˣ →* Rˣ, (∀ (x : Weil h) (g : Dec (F := F) A), (g : G F Ω) = x → χ (a x) = ψ g) ∧
      ∀ N, ∃ c, ∀ d, c ≤ d → ∀ y ∈ Uc _ d, (χ y : R) - 1 ∈ maximalIdeal R ^ N := by
  let f := ψ.comp (Subgroup.inclusion (Weil_le_Dec h))
  have key : ∀ N, ∃ c, ∀ d, c ≤ d → ∀ σ, a σ ∈ Uc _ d → (f σ : R) - 1 ∈ maximalIdeal R ^ N := fun N => by
    haveI : Finite (R ⧸ maximalIdeal R) := IsCNL.finite
    haveI : Finite (R ⧸ maximalIdeal R ^ N) := Ideal.finite_quotient_pow (IsNoetherian.noetherian _) N
    obtain ⟨c, hc⟩ := th_fin ha ((Units.map (Ideal.Quotient.mk (maximalIdeal R ^ N)).toMonoidHom).comp f) (by
      have := ((hψ N).comp_continuous (f := fun σ : Ine (F := F) A => Subgroup.inclusion (Weil_le_Dec h) (ineIncl h σ))
        (continuous_subtype_val.subtype_mk _)) {1}
      exact (congrArg IsOpen (Set.ext fun σ => Units.ext_iff)).mpr this)
    exact ⟨c, fun d hd σ hσ => Ideal.Quotient.eq.1 (congrArg Units.val (hc d hd σ hσ))⟩
  have hk : a.ker ≤ f.ker := fun σ hσ => by
    refine Units.ext (IsHausdorff.eq_iff_smodEq (I := maximalIdeal R).2 fun N => ?_)
    obtain ⟨c, hc⟩ := key N
    rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
    exact hc c le_rfl σ (by rw [show a σ = 1 from hσ]; exact one_mem _)
  have hf : ∀ x, a.liftOfSurjective ha.surj ⟨f, hk⟩ (a x) = f x := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply a _ _ ⟨f, hk⟩ x
  refine ⟨a.liftOfSurjective ha.surj ⟨f, hk⟩, fun x g e => (hf x).trans (congrArg ψ (Subtype.ext e.symm)), fun N => ?_⟩
  obtain ⟨c, hc⟩ := key N
  refine ⟨c, fun d hd y hy => ?_⟩
  obtain ⟨σ, rfl⟩ := ha.surj y
  rw [hf]
  exact hc d hd σ hy

private theorem th_eps {Γ R : Type} [TopologicalSpace Γ] [CommRing R] [IsLocalRing R] {l : ℕ} [Fact l.Prime]
    (j : ℤ_[l] →+* R) [IsLocalHom j] {e : Γ → ℤ_[l]} (he : Continuous e) :
    Alg.AdicCont (maximalIdeal R) fun g => j (e g) := fun N => by
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
  have ho : IsOpen {y : Γ | ‖e y - e x‖ < (l : ℝ) ^ (-(N : ℤ))} :=
    isOpen_lt (by fun_prop) continuous_const
  have hl : (0 : ℝ) < l := Nat.cast_pos.2 (Fact.out : l.Prime).pos
  filter_upwards [ho.mem_nhds (by simpa using pow_pos hl N)] with y hy
  refine Ideal.Quotient.eq.2 ?_
  have h1 : e y - e x ∈ maximalIdeal ℤ_[l] ^ N := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_singleton_pow]
    exact (PadicInt.norm_le_pow_iff_mem_span_pow _ _).1 hy.le
  rw [← map_sub]
  refine Ideal.pow_right_mono (I := (maximalIdeal ℤ_[l]).map j) ?_ N ?_
  · exact Ideal.map_le_iff_le_comap.2 fun z hz => map_nonunit j z hz
  · rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ h1

private theorem th_mul {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R} {f g : Γ → R}
    (hf : Alg.AdicCont I f) (hg : Alg.AdicCont I g) (i : ℕ) : Alg.AdicCont I fun x => f x * g x ^ i := fun N => by
  simp only [map_mul, map_pow]
  exact (hf N).mul ((hg N).comp (· ^ i))

private theorem th_diag (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    ∃ D : (glIwa k n).T →* (Fin n → kˣ), (∀ i y, D (eT k n i y) = Pi.mulSingle i (y : kˣ)) ∧
      ∀ c (t : (glIwa k n).T), (t : GL (Fin n) k) ∈ (glIwa k n).Tc c → ∀ i, D t i ∈ Uc k (c + 1) := by
  have hi : Function.Injective (diagT k (Fin n)) := fun s t e => by
    have := congrArg Units.val e
    rw [val_diagT, val_diagT] at this
    exact funext fun i => Units.ext (congrFun (Matrix.diagonal_injective this) i)
  let D : (glIwa k n).T →* (Fin n → kˣ) :=
    (MonoidHom.ofInjective hi).symm.toMonoidHom.comp (Subgroup.inclusion (glIwa k n).T_le)
  have hD : ∀ t, diagT k (Fin n) (D t) = t := fun t => MonoidHom.apply_ofInjective_symm hi _
  refine ⟨D, fun i y => hi (hD _), fun c t ht i => ?_⟩
  obtain ⟨y, e, hy⟩ := (glBridge k n ℂ 1).2.2.2.2.2.2.2.2.2 t
  have e2 : D t = fun i => (y i : kˣ) := hi <| by
    rw [hD, e]
    show (List.ofFn (diagT k (Fin n) ∘ fun i => Pi.mulSingle i (y i : kˣ))).prod = _
    rw [← List.map_ofFn, ← map_list_prod, List.prod_ofFn, Finset.univ_prod_mulSingle]
  rw [e2]
  exact hy c ht i

private theorem th_char' (ha : IsLocalArtin h a) {R : Type} [CommRing R] [IsCNL R] (ψ ε : Dec (F := F) A →* Rˣ)
    (hψ : Alg.AdicCont (maximalIdeal R) fun g => (ψ g : R)) (hε : Alg.AdicCont (maximalIdeal R) fun g => (ε g : R)) (i : ℕ) :
    ∃ χ : (w.adicCompletion F)ˣ →* Rˣ,
      (∀ (x : Weil h) (g : Dec (F := F) A), (g : G F Ω) = x → ψ g * ε g ^ i * χ (a x) = 1) ∧
      ∀ N, ∃ c, ∀ d, c ≤ d → ∀ y ∈ Uc _ d, (χ y : R) - 1 ∈ maximalIdeal R ^ N := by
  obtain ⟨χ, h1, h2⟩ := th_char ha (ψ * ε ^ i)⁻¹ fun N => by
    refine (congrArg IsLocallyConstant (funext fun g => ?_)).mpr ((th_mul hψ hε i N).comp_continuous continuous_inv)
    refine congrArg (Ideal.Quotient.mk _) ?_
    simp only [MonoidHom.inv_apply, ← map_inv]
    simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, Units.val_pow_eq_pow_val]
  exact ⟨χ, fun x g e => by rw [h1 x g e]; exact mul_inv_cancel _, h2⟩

private theorem th_torus (n : ℕ) {V : Type} [Fintype V] (S : V → Plc F) {R : Type} [CommRing R] [IsLocalRing R]
    (χ : ∀ v, Fin n → ((S v).adicCompletion F)ˣ →* Rˣ)
    (hc : ∀ v i N, ∃ c, ∀ d, c ≤ d → ∀ y ∈ Uc _ d, (χ v i y : R) - 1 ∈ maximalIdeal R ^ N) :
    ∃ θ : (iwS n S).T →* Rˣ, (∀ v i y, θ (eV n S v i y) = χ v i y) ∧ (iwS n S).ContChar θ := by
  classical
  choose D hD hDc using fun v => th_diag ((S v).adicCompletion F) n
  let p : ∀ v, (iwS n S).T →* (glIwa ((S v).adicCompletion F) n).T := fun v =>
    ((Pi.evalMonoidHom (fun v => GLw n (S v)) v).comp (iwS n S).T.subtype).codRestrict _ fun t => t.2 v trivial
  let θ : (iwS n S).T →* Rˣ := ∏ v, ∏ i, (χ v i).comp ((Pi.evalMonoidHom _ i).comp ((D v).comp (p v)))
  have hθ : ∀ t, θ t = ∏ v, ∏ i, χ v i (D v (p v t) i) := fun t => by
    simp only [θ, MonoidHom.finsetProd_apply, MonoidHom.comp_apply, Pi.evalMonoidHom_apply]
  refine ⟨θ, fun v i y => ?_, fun N => ?_⟩
  · have e : D v (p v (eV n S v i y)) = Pi.mulSingle i (y : ((S v).adicCompletion F)ˣ) :=
      (congrArg (D v) (Subtype.ext (Pi.mulSingle_eq_same (M := fun v => GLw n (S v)) _ _))).trans (hD v i y)
    rw [hθ, Finset.prod_eq_single v, Finset.prod_eq_single i]
    · rw [e, Pi.mulSingle_eq_same]
    · intro j _ hj
      rw [e, Pi.mulSingle_eq_of_ne hj, map_one]
    · simp
    · intro v' _ hv
      rw [show p v' (eV n S v i y) = 1 from Subtype.ext (Pi.mulSingle_eq_of_ne (M := fun v => GLw n (S v)) hv _)]
      simp
    · simp
  · choose d hd using fun x : V × Fin n => hc x.1 x.2 N
    refine ⟨Finset.univ.sup d, fun t ht => ?_⟩
    refine Ideal.Quotient.eq.1 ?_
    rw [hθ]
    simp only [Units.coe_prod, map_prod, map_one]
    refine Finset.prod_eq_one fun v _ => Finset.prod_eq_one fun i _ => ?_
    exact Ideal.Quotient.eq.2 (hd (v, i) _ ((Finset.le_sup (Finset.mem_univ _)).trans (Nat.le_succ _)) _
      (hDc v _ (p v t) (ht v trivial) i))

private theorem th_free {Γ Ga Gp A : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) [CommRing A] {m : ℕ}
    (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ) {U : Subgroup X.Ub} (hU : X.Neat U) : X.Free τ θ U := by
  intro g γ u hu b hb e
  obtain ⟨rfl, rfl⟩ := hU g γ u hu b hb e
  refine ⟨one_mem _, one_mem _, ?_⟩
  rw [show (⟨1, one_mem _⟩ : X.I.T) = 1 from rfl, map_one, map_one]
  simp

end SlopeTestRemainingChoices

theorem UpperTheory.V.Hi.thetaEx :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), ∀ (r : Resid V.frame c.O n) (Λ : LamObj r), ∃ θ : (hset Q τ₀).X.I.T →* Λ.Λˣ, IsTheta Q τ₀ Λ θ ∧ (hset Q τ₀).IsWt θ := by
  intro H l _ L Ω _ _ _ _ _ _ s n hn V Q c m τ₀ r Λ
  haveI : Finite (ResidueField c.O) := (abelian₂.dvr_finite l c.O).2.1
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (abelian₂.dvr_finite l c.O).2.2.2.2.2
  haveI : IsCNL Λ.Λ := IsCNL.ofCO c.O Λ.Λ
  choose ψ hψ hκ using Λ.inert
  have ha : ∀ v : V.frame.Vl, IsLocalArtin (s.hw v.1) (artOf (s.hw v.1)) := fun v =>
    Classical.epsilon_spec (Loc.localArtinReciprocity H (s.hw v.1))
  choose χ hχ hc using fun (v : V.frame.Vl) (i : Fin n) =>
    th_char' (ha v) (ψ v i) ((hset Q τ₀).epsV Λ.Λ v) (hψ v i).cont
      (th_eps ((algebraMap c.O Λ.Λ).comp (algebraMap ℤ_[l] c.O))
        (e := fun g : Dec (F := L) (s.A v.1) => (cycZ L Ω l g : ℤ_[l]))
        (Units.continuous_val.comp ((continuous_cycZ L Ω l).comp continuous_subtype_val))) i
  obtain ⟨θ, h1, h2⟩ := th_torus n (fun v : V.frame.Vl => s.w v.1) χ hc
  refine ⟨θ, fun v i x g hg y e1 e2 => ?_, h2, fun K => th_free _ _ _ (neatU l L Ω s n hn V Q c m τ₀ K)⟩
  have e3 := hχ v i x g e1
  rw [e2, ← h1] at e3
  rw [hκ]
  exact e3
end
