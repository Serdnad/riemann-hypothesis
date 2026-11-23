module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle037
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle089
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle086
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2AtW
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PlaceBetween
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

section Helpers
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem ae_abs {A R P Lev B ι : Type} [CommRing A] [CommRing R] [AddCommGroup P] [Module A P] [Nonempty Lev] [Group B]
    (MK : Lev → Submodule A P) (S : Submodule A P) (op : ι → Module.End A P) (ρ : Representation A B S) (κ : Lev → Subgroup B)
    (hfix : ∀ K, (fixd ρ (κ K)).map S.subtype = MK K) (hex : ∀ f : S, ∃ K, (f : P) ∈ MK K)
    (hinf : ∀ K K', ∃ K'', κ K'' ≤ κ K ∧ κ K'' ≤ κ K') (hconj : ∀ K g, ∃ K', ∀ k ∈ κ K', g⁻¹ * k * g ∈ κ K)
    (hop : ∀ g i (z z' : S), (z' : P) = op i z → (ρ g z' : P) = op i (ρ g z))
    (μ : ∀ K, R →+* Module.End A (MK K))
    (hμ : ∀ K K' (φ : MK K →ₗ[A] MK K'), Function.Injective φ →
      (∀ i (y y' : MK K), (y' : P) = op i y → (φ y' : P) = op i (φ y)) → ∀ t y, φ (μ K t y) = μ K' t (φ y)) :
    ∃ α : R →+* Module.End A S, (∀ t g z, α t (ρ g z) = ρ g (α t z)) ∧
      ∀ K t (y : MK K) (z : S), (z : P) = y → (α t z : P) = μ K t y := by
  have hle : ∀ K, MK K ≤ S := fun K => by
    rw [← hfix]
    exact Submodule.map_subtype_le _ _
  have hmem : ∀ K (z : S), (z : P) ∈ MK K ↔ z ∈ fixd ρ (κ K) := fun K z => by
    rw [← hfix]
    exact ⟨fun ⟨y, hy, e⟩ => Subtype.ext e ▸ hy, fun h => ⟨z, h, rfl⟩⟩
  let e : ∀ K, (MK K).comap S.subtype ≃ₗ[A] MK K := fun K => Submodule.comapSubtypeEquivOfLe (hle K)
  have he : ∀ K y, (e K y : P) = (y : S) := fun _ _ => rfl
  have he' : ∀ K y, (((e K).symm y : S) : P) = y := fun K y => by rw [← he, LinearEquiv.apply_symm_apply]
  obtain ⟨α, hα⟩ := levelUR2Glue A R S Lev (fun K => (MK K).comap S.subtype)
    (fun K => (e K).symm.conjRingEquiv.toRingHom.comp (μ K)) hex
    (fun K K' => by
      obtain ⟨K'', h1, h2⟩ := hinf K K'
      exact ⟨K'', fun z hz => (hmem _ z).2 fun k hk => (hmem _ z).1 hz k (h1 hk),
        fun z hz => (hmem _ z).2 fun k hk => (hmem _ z).1 hz k (h2 hk)⟩)
    (fun K K' h t y => by
      have h' : MK K ≤ MK K' := fun x hx => h (x := ⟨x, hle K hx⟩) hx
      have := hμ K K' (Submodule.inclusion h') (Submodule.inclusion_injective h') (fun i y y' hy => hy) t (e K y)
      refine Subtype.ext ?_
      exact (he' K' _).trans ((congrArg Subtype.val this).symm.trans (he' K _).symm))
  have h2 : ∀ K t (y : MK K) (z : S), (z : P) = y → (α t z : P) = μ K t y := fun K t y z hz => by
    have hy : y = e K ⟨z, show (z : P) ∈ MK K from hz ▸ y.2⟩ := Subtype.ext hz.symm
    rw [hy]
    exact (congrArg Subtype.val (hα K t ⟨z, show (z : P) ∈ MK K from hz ▸ y.2⟩)).trans (he' K _)
  refine ⟨α, fun t g z => ?_, h2⟩
  obtain ⟨K, hK⟩ := hex z
  obtain ⟨K', hK'⟩ := hconj K g
  let φ : MK K →ₗ[A] MK K' := (S.subtype ∘ₗ ρ g ∘ₗ Submodule.inclusion (hle K)).codRestrict _ fun y =>
    (hmem K' _).2 fun k hk => by
      have := (hmem K (Submodule.inclusion (hle K) y)).1 y.2 _ (hK' k hk)
      change ρ k (ρ g _) = ρ g _
      conv_rhs => rw [← this]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, ← mul_assoc, mul_inv_cancel_left]
  have hφ : ∀ y, (φ y : P) = ρ g (Submodule.inclusion (hle K) y) := fun _ => rfl
  have hinj : Function.Injective φ := fun y y' h => by
    have h3 : ρ g (Submodule.inclusion (hle K) y) = ρ g (Submodule.inclusion (hle K) y') :=
      Subtype.ext (by rw [← hφ, ← hφ, h])
    have h4 := congrArg (ρ g⁻¹) h3
    simp only [Representation.inv_self_apply] at h4
    exact Submodule.inclusion_injective _ h4
  have h5 := hμ K K' φ hinj (fun i y y' hy => hop g i _ _ hy) t ⟨z, hK⟩
  refine Subtype.ext ?_
  rw [h2 K' t (φ ⟨z, hK⟩) (ρ g z) rfl, ← h5, hφ]
  exact congrArg (fun x => (ρ g x : P)) (Subtype.ext (h2 K t ⟨z, hK⟩ z rfl).symm)

private theorem ae_ind {Q : Type} [Fintype Q] [DecidableEq Q] {G : Q → Type} [∀ q, Group (G q)] (p : (∀ q, G q) → Prop)
    (h1 : p 1) (hm : ∀ g g', p g → p g' → p (g * g')) (hs : ∀ q g, p (Pi.mulSingle q g)) (g : ∀ q, G q) : p g := by
  rw [← Finset.noncommProd_mulSingle g]
  exact Finset.noncommProd_induction _ _ _ p hm h1 fun q _ => hs q _

private theorem ae_gen {Q : Type} [Fintype Q] [DecidableEq Q] {G : Q → Type} [∀ q, Group (G q)] {A P ι : Type} [CommRing A]
    [AddCommGroup P] [Module A P] (S : Submodule A P) (op : ι → Module.End A P) (ρ : Representation A (∀ q, G q) S)
    (s : ∀ q, G q → Module.End A P) (hρ : ∀ q g f, (ρ (Pi.mulSingle q g) f : P) = s q g f)
    (hop : ∀ q g i, Commute (s q g) (op i)) :
    ∀ g i (z z' : S), (z' : P) = op i z → (ρ g z' : P) = op i (ρ g z) :=
  ae_ind _ (fun i z z' h => by simpa using h)
    (fun g g' hg hg' i z z' h => by
      rw [map_mul]
      exact hg i _ _ (hg' i z z' h))
    (fun q g i z z' h => by rw [hρ, hρ, h, ← Module.End.mul_apply, (hop q g i).eq, Module.End.mul_apply])

section Top

variable {Q : Type} {G : Q → Type} [∀ q, Group (G q)] [∀ q, TopologicalSpace (G q)] [∀ q, IsTopologicalGroup (G q)]

private theorem ae_inf (K K' : {K : ∀ q, Subgroup (G q) // ∀ q, IsOpen (K q : Set (G q)) ∧ IsCompact (K q : Set (G q))}) :
    ∃ K'' : {K : ∀ q, Subgroup (G q) // ∀ q, IsOpen (K q : Set (G q)) ∧ IsCompact (K q : Set (G q))},
      Subgroup.pi Set.univ K''.1 ≤ Subgroup.pi Set.univ K.1 ∧ Subgroup.pi Set.univ K''.1 ≤ Subgroup.pi Set.univ K'.1 :=
  ⟨⟨fun q => K.1 q ⊓ K'.1 q, fun q => ⟨(K.2 q).1.inter (K'.2 q).1,
      (K.2 q).2.inter_right ((K'.1 q).isClosed_of_isOpen (K'.2 q).1)⟩⟩,
    fun _ hk q hq => (hk q hq).1, fun _ hk q hq => (hk q hq).2⟩

private theorem ae_conj (K : {K : ∀ q, Subgroup (G q) // ∀ q, IsOpen (K q : Set (G q)) ∧ IsCompact (K q : Set (G q))})
    (g : ∀ q, G q) : ∃ K' : {K : ∀ q, Subgroup (G q) // ∀ q, IsOpen (K q : Set (G q)) ∧ IsCompact (K q : Set (G q))},
      ∀ k ∈ Subgroup.pi Set.univ K'.1, g⁻¹ * k * g ∈ Subgroup.pi Set.univ K.1 :=
  ⟨⟨fun q => (K.1 q).comap (MulAut.conj (g q)⁻¹).toMonoidHom, fun q => by
      let e := (Homeomorph.mulLeft (g q)⁻¹).trans (Homeomorph.mulRight (g q)⁻¹⁻¹)
      exact ⟨(K.2 q).1.preimage e.continuous, e.isCompact_preimage.2 (K.2 q).2⟩⟩,
    fun k hk q hq => by simpa using hk q hq⟩

end Top

private theorem ae_commU {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {A : Type} [CommRing A] {m : ℕ}
    (τ : X.Ub →* GL (Fin m) A) (u : X.Ub) (b : Gp) : Commute (X.ra τ u) (X.U A m b) := by
  unfold Frame.U Iwa.uOp
  refine finsum_induction (fun t => Commute (X.ra τ u) t) (Commute.zero_right _) (fun _ _ => Commute.add_right) fun q => ?_
  refine LinearMap.ext fun f => funext fun g => ?_
  change (τ u : Matrix (Fin m) (Fin m) A) *ᵥ f (g * ((u : Ga), 1) * (1, _)) =
    (τ u : Matrix (Fin m) (Fin m) A) *ᵥ f (g * (1, _) * ((u : Ga), 1))
  simp [mul_assoc]

private theorem ae_dc {A H H' M : Type} [CommRing A] [Group H] [Group H'] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (s : H' →* H) (u : H) (h : ∀ g, Commute u (s g)) (K K' : Subgroup H') (x : H') :
    Commute (ρ u) (dc (ρ.comp s) K K' x) :=
  finsum_induction (fun t => Commute (ρ u) t) (Commute.zero_right _) (fun _ _ => Commute.add_right) fun _ => (h _).map ρ

private theorem ae_bot {A R P : Type} [CommRing A] [CommRing R] [AddCommGroup P] [Module A P] {Y : Submodule A P} (h : Y = ⊥)
    (lam : A → R) : ∃ μ : R →+* Module.End A Y, (∀ b y, μ (lam b) y = b • y) ∧ Subsingleton Y := by
  haveI : Subsingleton Y := h ▸ inferInstance
  exact ⟨⟨⟨⟨fun _ => 0, Subsingleton.elim _ _⟩, fun _ _ => Subsingleton.elim _ _⟩, rfl, fun _ _ => Subsingleton.elim _ _⟩,
    fun _ _ => Subsingleton.elim _ _, this⟩

private theorem ae_mu {O A R P ι : Type} [CommRing O] [CommRing A] [CommRing R] [AddCommGroup P] [Module A P]
    {Y : Submodule A P} {op : ι → Module.End A P} [Fact (CommOn Y op)] [Algebra O R] [Algebra O (heckeAlg Y op)]
    (f : R →ₐ[O] heckeAlg Y op) (lam : A → R) (hl : ∀ b, f (lam b) = algebraMap A _ b) :
    ∃ μ : R →+* Module.End A Y, (∀ t, μ t = (f t : Module.End A Y)) ∧ ∀ b y, μ (lam b) y = b • y := by
  refine ⟨(heckeAlg Y op).val.toRingHom.comp f.toRingHom, fun _ => rfl, fun b y => ?_⟩
  change (f (lam b) : Module.End A Y) y = _
  rw [hl]
  rfl

private theorem ae_nt {A P ι : Type} [CommRing A] [AddCommGroup P] [Module A P] {Y : Submodule A P}
    {op : ι → Module.End A P} [Nontrivial (heckeAlg Y op)] : ¬ Subsingleton Y := fun _ =>
  absurd (inferInstance : Subsingleton (heckeAlg Y op)) (not_subsingleton _)

private theorem ae_zero {A M N : Type} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (h : Subsingleton M) (φ : M →ₗ[A] N) (s : Module.End A M) (t : Module.End A N) (y : M) : φ (s y) = t (φ y) := by
  rw [Subsingleton.elim y 0, map_zero, map_zero, map_zero]

end Helpers

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


section

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ)
  (a : H.Op → c.O) {R : Type} [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R H.Gq)
  (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ)

private def ae_Ok (K : H.Lev) (μ : R →+* Module.End A (H.MK θ a K)) : Prop :=
  Subsingleton (H.MK θ a K) ∨
    ∃ (_ : Fact (CommOn (H.MK θ a K) (H.op A))) (_ : Alg.IsCO c.O (H.TK θ a K)) (f : R →ₐ[c.O] H.TK θ a K),
      H.IsMap θ a K D₀ ψ₀ f ∧ ∀ t, μ t = (f t : Module.End A (H.MK θ a K))

private theorem ae_ex (lam : A →ₐ[c.O] R) (K : H.Lev) (J : Ideal R) (hJ : H.IsJ θ a K D₀ ψ₀ lam J) :
    ∃ μ : R →+* Module.End A (H.MK θ a K), (∀ b y, μ (lam b) y = b • y) ∧ ae_Ok H θ a D₀ ψ₀ K μ := by
  rcases hJ with h | ⟨i1, i2, f, -, hf, -, hl, -⟩
  · exact (ae_bot (A := A) (R := R) (P := H.X.Fn A H.m) (Y := H.MK θ a K) h.1 lam).imp fun μ h => ⟨h.1, .inl h.2⟩
  · exact (ae_mu (A := A) (P := H.X.Fn A H.m) (Y := H.MK θ a K) (op := H.op A) f lam hl).imp
      fun μ h => ⟨h.2, .inr ⟨i1, i2, f, hf, h.1⟩⟩

private theorem ae_cmp (hN : GlobalTheory.Mem.LiteralAutomorphy.LitN) (hH : H.Ax) (hθ : H.IsWt θ)
    (hU : ∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (f g : R →ₐ[c.O] T),
      D₀.map f.toRingHom = D₀.map g.toRingHom →
      (∀ v i, W.pushCh f.toRingHom (ψ₀ v i) = W.pushCh g.toRingHom (ψ₀ v i)) → f = g)
    (K K' : H.Lev) (μ : R →+* Module.End A (H.MK θ a K)) (μ' : R →+* Module.End A (H.MK θ a K'))
    (h : ae_Ok H θ a D₀ ψ₀ K μ) (h' : ae_Ok H θ a D₀ ψ₀ K' μ') (φ : H.MK θ a K →ₗ[A] H.MK θ a K') (hφ : Function.Injective φ)
    (hc : ∀ i (y y' : H.MK θ a K), (y' : H.X.Fn A H.m) = H.op A i y → (φ y' : H.X.Fn A H.m) = H.op A i (φ y)) (t : R)
    (y : H.MK θ a K) : φ (μ t y) = μ' t (φ y) := by
  rcases h with h | ⟨i1, i2, f, hf, e⟩
  · exact ae_zero h φ (μ t) (μ' t) y
  rcases h' with h | ⟨i1', i2', f', hf', e'⟩
  · exact h.elim _ _
  rw [e, e']
  exact levelUR2Compat hN L Ω l n c H hH A θ hθ a K K' R D₀ ψ₀ hU f f' hf hf' φ hφ (fun i y => hc i y _ rfl) t y

private theorem ae_out (K : H.Lev) (μ : R →+* Module.End A (H.MK θ a K)) (h : ae_Ok H θ a D₀ ψ₀ K μ)
    [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)] :
    ∃ f : R →ₐ[c.O] H.TK θ a K, H.IsMap θ a K D₀ ψ₀ f ∧ ∀ t, μ t = (f t : Module.End A (H.MK θ a K)) := by
  rcases h with h | ⟨_, _, h⟩
  · exact absurd h (ae_nt (op := H.op A))
  · exact h

private theorem ae_op (hH : H.Ax) (q : H.Q) (g : GLw n (H.wq q)) (i : H.Op) :
    Commute (H.X.ra (H.τA A) (H.sec (H.wq q) g)) (H.op A i) := by
  rcases i with x | x
  · exact ae_dc _ _ _ (hH.sectionsCommuteAtSplit q _ x.1.2 g) _ _ _
  · exact ae_commU _ _ _ _

end

theorem UpperTheory.V.Hi.levelUR2ActEx :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (a : H.Op → c.O) [DecidableEq H.Q] (ρ : Representation A (GV n H.wq) (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m))), (∀ q g f, (ρ (Pi.mulSingle q g) f : H.X.Fn A H.m) = H.X.ra (H.τA A) (H.sec (H.wq q) g) f) → (∀ K : H.Lev, (fixd ρ (Subgroup.pi Set.univ K.1)).map (Submodule.subtype _) = H.MK θ a K) → (∀ f : (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m)), ∃ K, (f : H.X.Fn A H.m) ∈ H.MK θ a K) → ∀ (R : Type) [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R H.Gq) (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ) (lam : A →ₐ[c.O] R), (∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (f g : R →ₐ[c.O] T), D₀.map f.toRingHom = D₀.map g.toRingHom → (∀ v i, W.pushCh f.toRingHom (ψ₀ v i) = W.pushCh g.toRingHom (ψ₀ v i)) → f = g) → (∀ K, ∃ J, H.IsJ θ a K D₀ ψ₀ lam J) → ∃ α : R →+* Module.End A (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m)), (∀ b z, α (lam b) z = b • z) ∧ (∀ t g z, α t (ρ g z) = ρ g (α t z)) ∧ ∀ (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)], ∃ f : R →ₐ[c.O] H.TK θ a K, H.IsMap θ a K D₀ ψ₀ f ∧ ∀ t (y : H.MK θ a K) (z : (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m))), (z : H.X.Fn A H.m) = y → (α t z : H.X.Fn A H.m) = ((f t : Module.End A (H.MK θ a K)) y : H.MK θ a K) := by
  intro hN L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ a _ ρ hρ hfix hex R _ _ D₀ ψ₀ lam hU hJ
  haveI : Nonempty H.Lev := ⟨⟨fun q => KO _ (Fin n), fun q => ⟨GlobalTheory.SplitFlip.isOpen_KO, GlobalTheory.SplitFlip.isCompact_KO⟩⟩⟩
  choose μ hμ1 hμ2 using fun K => ae_ex H θ a D₀ ψ₀ lam K _ (hJ K).choose_spec
  obtain ⟨α, h1, h2⟩ := ae_abs (H.MK θ a) _ (H.op A) ρ (fun K : H.Lev => Subgroup.pi Set.univ K.1) hfix hex ae_inf ae_conj
    (ae_gen _ (H.op A) ρ (fun q g => H.X.ra (H.τA A) (H.sec (H.wq q) g)) hρ (ae_op H hH)) μ
    (fun K K' => ae_cmp H θ a D₀ ψ₀ hN hH hθ hU K K' _ _ (hμ2 K) (hμ2 K'))
  refine ⟨α, fun b z => ?_, h1, fun K i1 i2 => ?_⟩
  · obtain ⟨K, hK⟩ := hex z
    exact Subtype.ext ((h2 K _ ⟨z, hK⟩ z rfl).trans (congrArg Subtype.val (hμ1 K b ⟨z, hK⟩)))
  · obtain ⟨f, hf, e⟩ := ae_out H θ a D₀ ψ₀ K _ (hμ2 K)
    refine ⟨f, hf, fun t y z hz => ?_⟩
    rw [← e]
    exact h2 K t y z hz
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


private theorem raF_big {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {d m : ℕ}
    (τ : X.Ub →* GL (Fin m) ℂ) (ξ : Gp →* GL (Fin d) ℂ) (U : Subgroup X.Ub) (x : X.Ub) (hx : ∀ u ∈ U, Commute u x)
    (F : Fin m → X.Fn ℂ d) (hF : F ∈ Submodule.pi Set.univ (fun _ => X.AF ξ) ⊓ fixd (X.raF d τ) U) :
    X.raF d τ x F ∈ Submodule.pi Set.univ (fun _ => X.AF ξ) ⊓ fixd (X.raF d τ) U := by
  refine ⟨fun i _ => ?_, fun u hu => ?_⟩
  · have h : X.raF d τ x F i = ∑ j, (τ x : Matrix (Fin m) (Fin m) ℂ) i j • fun g => F j (g * ((x : Ga), 1)) := by
      funext g k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rfl
    change X.raF d τ x F i ∈ X.AF ξ
    rw [h]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ fun γ g => ?_
    have := hF.1 j trivial γ (g * ((x : Ga), 1))
    simpa only [mul_assoc] using this
  · rw [← Module.End.mul_apply, ← map_mul, (hx u hu).eq, map_mul, Module.End.mul_apply, hF.2 u hu]

private theorem big_atW {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (hA : H.Ax) (ι : Qbar l ≃+* ℂ) {d : ℕ} (ξ : GV n H.Sl →* GL (Fin d) ℂ)
    (q : H.Q) (g : GLw n (H.wq q)) (F : Fin H.m → H.X.Fn ℂ d) (hF : F ∈ H.Big ι ξ) : H.atW ι d (H.wq q) g F ∈ H.Big ι ξ :=
  raF_big H.X (H.τC ι) ξ H.UQ (H.sec (H.wq q) g) (fun u hu => hA.Q_UQ q u hu g) F hF

private noncomputable def formL {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} {V : s.Lev} (ι : Qbar l ≃+* ℂ) {lam : Wt L l n} {d : ℕ}
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) :
    (Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) →ₗ[ℂ]
      Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) →ₗ[ℂ] (UA L n → ℂ) :=
  LinearMap.mk₂ ℂ (toForm ι e)
    (fun F F' ℓ => funext fun g => by simp only [toForm, Pi.add_apply, map_add (f := _)])
    (fun a F ℓ => funext fun g => by simp only [toForm, Pi.smul_apply, map_smul])
    (fun F ℓ ℓ' => rfl) (fun a F ℓ => rfl)

theorem UpperTheory.V.Hi.partUR2IsoQ :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    (hset Q τ₀).Ax → ∀ (q : Q.Q) (τ : SmIrr (GLw n (Q.wq q))), IsCompAlong σ (locU n (Q.wq q)) ((cLoc (Q.wq q)).comp (locU n (Q.wq q)).subtype) τ.ρ → IsoSum ((hset Q τ₀).atW ι d (Q.wq q)) (YOf Q ι τ₀ e ξ σ) τ := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c ι m τ₀ lam d e ξ hξ σ hσ hA q τ hτ
  have hS' : (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := by
    rw [Q.range]
    exact Or.inr ⟨q, rfl⟩
  have hsp : IsSplitAt (Q.wq q) := UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA _) (V.split _ hS') _ rfl
  obtain ⟨j, hj1, hj2, -, hj3⟩ := (secU l L Ω s n hn _ hsp).1
  have hiso := UpperTheory.isoSum_restriction_of_local_component_unitary L n σ hσ _ j hj1 hj2 hj3 τ hτ
  have hmem := partUR2Mem l L Ω s n hn V Q c ι m τ₀ lam d e ξ σ
  have hat := partUR2AtW l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ _ hsp (Q.notS q) j hj1 hj2
  have hinj := (formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ _ fun _ => rfl).1
  let b := ((Pi.basisFun ℂ (Fin d)).map e).dualBasis
  let φ : Fin m × Fin d → (Fin m → Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) →ₗ[ℂ] (UA L n → ℂ) :=
    fun x => ((formL ι e).flip (b x.2)).comp (LinearMap.proj x.1)
  refine UpperTheory.isoSum_of_injective_equivariant_family _ _ _ _ ((RU L n).comp j) _ σ τ (Fin m × Fin d) φ hiso (fun g F hF => ?_) (fun x F hF => ?_)
    (fun x g F _ => ?_) (fun F hF h0 => ?_)
  · obtain ⟨h1, h2⟩ := (hmem F).1 hF
    refine (hmem _).2 ⟨big_atW (hset Q τ₀) hA ι ξ q g F h1, fun i ℓ => ?_⟩
    refine (hat F g i ℓ).symm ▸ ?_
    exact hσ.stable _ _ (h2 i ℓ)
  · exact ((hmem F).1 hF).2 x.1 (b x.2)
  · exact hat F g x.1 (b x.2)
  · refine funext fun i => hinj (F i) (((hmem F).1 hF).1.1 i trivial) fun ℓ => ?_
    have h : formL ι e (F i) = 0 := b.ext fun k => h0 (i, k)
    exact LinearMap.congr_fun h ℓ
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem UpperTheory.V.Hi.levelUR2Faith :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) [DecidableEq Q.Q] (c : Coef l) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (K : (hset Q τ₀).Lev) (k : GV n Q.wq) (j : GV n Q.wq →* Ub n s), (∀ q g, j (Pi.mulSingle q g) = sec n s (Q.wq q) g) → j k ∈ (hset Q τ₀).lev K → k ∈ Subgroup.pi Set.univ K.1 := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q _ c m τ₀ K k j hj hk
  have hS : ∀ q : Q.Q, (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := fun q => by
    rw [Q.range]
    exact Or.inr ⟨q, rfl⟩
  have hsec := fun q : Q.Q => (secU l L Ω s n hn (Q.wq q)
    (UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA _) (V.split _ (hS q)) _ rfl)).2 (Q.notS q)
  have h1 : ∀ (q : Q.Q) (g : GLw n (Q.wq q)) (w : Plc L), w.under (𝓞 (Lp L)) ≠ (Q.wq q).under (𝓞 (Lp L)) →
      CaseU.cmp n w ((sec n s (Q.wq q) g : Ub n s) : Ga l L n) = 1 := fun q g w hw =>
    MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 ((hsec q).2.2 g) w) hw)
  have key : ∀ q : Q.Q, ((CaseU.cmp n (Q.wq q)).comp (Ub n s).subtype).comp j =
      Pi.evalMonoidHom (fun q : Q.Q => GLw n (Q.wq q)) q := fun q => by
    refine MonoidHom.pi_ext fun q' g => ?_
    change CaseU.cmp n (Q.wq q) ((j (Pi.mulSingle q' g) : Ub n s) : Ga l L n) =
      (Pi.mulSingle q' g : ∀ q : Q.Q, GLw n (Q.wq q)) q
    rw [hj]
    by_cases h : q = q'
    · subst h
      rw [Pi.mulSingle_eq_same]
      exact (hsec q).2.1 g
    · rw [Pi.mulSingle_eq_of_ne h]
      exact h1 q' g _ fun h' => h (Q.inj h')
  intro q _
  have h2 := (levelUR2LevOut l L Ω s n hn V Q c m τ₀ K (j k) hk).2 q
  have h3 : CaseU.cmp n (Q.wq q) ((j k : Ub n s) : Ga l L n) = k q := DFunLike.congr_fun (key q) k
  rw [h3] at h2
  exact h2
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


private theorem form_inj {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} (V : s.Lev) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) (d : ℕ)
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (hs : Function.Surjective fun k : finU (E := L) (n := n) =>
      (((away l L n).rangeRestrict k, fun v : V.frame.Vl => cLoc (s.w v.1) k) : Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1)))
    (F F' : Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) (h : ∀ ℓ, toForm ι e F ℓ = toForm ι e F' ℓ) :
    F = F' := by
  funext y
  obtain ⟨k, rfl⟩ := hs y
  refine e.injective ?_
  have hR : ∀ u, infRep (V := V) ι lam k (infRep (V := V) ι lam (k : UA L n)⁻¹ u) = u := fun u => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  refine (hR _).symm.trans (Eq.trans (congrArg _ ?_) (hR _))
  refine sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => ?_)
  rw [map_sub]
  exact sub_eq_zero.2 (congrFun (h ℓ) k)

private noncomputable def formLin {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} (V : s.Lev) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) (d : ℕ)
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (m : ℕ) (i : Fin m)
    (ℓ : Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))) :
    (Fin m → Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) →ₗ[ℂ] (UA L n → ℂ) where
  toFun F := toForm ι e (F i) ℓ
  map_add' F F' := funext fun g => by
    simp only [toForm, Pi.add_apply, map_add (f := _)]
  map_smul' a F := funext fun g => by
    simp only [toForm, Pi.smul_apply, map_smul, RingHom.id_apply]

private theorem push (L : Type) [Field L] [NumberField L] (n : ℕ) (w : Plc L) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ (GLw n w) M) (M' : Type) [AddCommGroup M'] [Module ℂ M'] (ρ' : Representation ℂ (GLw n w) M')
    (σ : Submodule ℂ M') (τ : SmIrr (GLw n w)) (hiso : IsoSum ρ' σ τ) (j : ℕ) (a : ℂ)
    (ha : ∀ v ∈ fixd τ.ρ (KO (w.adicCompletion L) (Fin n)), sphOp τ.ρ j v = a • v) (f : M →ₗ[ℂ] M')
    (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (F : M) (hfix : ∀ k ∈ KO (w.adicCompletion L) (Fin n), ρ k F = F) (hm : f F ∈ σ) :
    f (sphOp ρ j F) = f (a • F) := by
  have h3 := (UpperTheory.V.Hi.partUR2Abs L n w M ρ ⊥ τ bot_le).2.2.1 M' ρ' f.toAddMonoidHom hf j F
  have h2 := (UpperTheory.V.Hi.partUR2Abs L n w M' ρ' σ τ hiso).2.1 j a ha (f F)
    (Submodule.mem_inf.2 ⟨hm, fun k hk => (hf k F).symm.trans (congrArg f (hfix k hk))⟩)
  exact h3.trans (h2.trans (f.map_smul a F).symm)

theorem UpperTheory.V.Hi.partUR2Sph :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    (hset Q τ₀).Ax → ∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → IsSplitAt w → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ →
    ∀ (j : ℕ) (a : ℂ), (∀ v ∈ fixd τ.ρ (KO (w.adicCompletion L) (Fin n)), sphOp τ.ρ j v = a • v) → ∀ F ∈ YOf Q ι τ₀ e ξ σ, sphOp ((hset Q τ₀).atW ι d w) j F = a • F := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c ι m τ₀ lam d e ξ hξ σ hσ hAx w hw hsp τ hτ j a ha F hF
  obtain ⟨j0, hj1, hj2, -, hj3⟩ := (UpperTheory.V.Hi.secU l L Ω s n hn w hsp).1
  have hS : w.under (𝓞 (Lp L)) ∉ s.S := fun h => hw (Q.range ▸ Or.inl h)
  have hat := UpperTheory.V.Hi.partUR2AtW l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ w hsp hS j0 hj1 hj2
  obtain ⟨hB, hm⟩ := (UpperTheory.V.Hi.partUR2Mem l L Ω s n hn V Q c ι m τ₀ lam d e ξ σ F).1 hF
  have hiso := UpperTheory.isoSum_restriction_of_local_component_unitary L n σ hσ w j0 hj1 hj2 hj3 τ hτ
  have hs := (UpperTheory.V.Hi.formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ _ (fun _ => rfl)).2.2.2.1
  have hfix : ∀ k ∈ KO (w.adicCompletion L) (Fin n), (hset Q τ₀).atW ι d w k F = F := fun k hk =>
    hB.2 _ (hAx.W_le w ⟨hw, hsp⟩ (Subgroup.mem_map_of_mem _ hk))
  funext i
  refine form_inj V ι lam d e hs _ _ fun ℓ => ?_
  exact push L n w (Fin m → Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) ((hset Q τ₀).atW ι d w) _
    ((RU L n).comp j0) σ τ hiso j a ha (formLin V ι lam d e m i ℓ) (fun g v => hat v g i ℓ) F hfix (hm i ℓ)
end
