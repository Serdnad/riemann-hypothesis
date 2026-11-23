module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle014
public import Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.MemTypeSubspaceIffUnipotentCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle090
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle297
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionInjectiveSaturatedInter
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle323
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle324
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod

@[expose] public section

section

noncomputable section

open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.IdemAlg

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X)

theorem card_eq : D.what₂.restRowsFiniteGroupCard = Nat.card (G0g N) := by
  have : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  rw [N.restN_card_levelGroup_eq, Nat.card_pi, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  change _ = ∏ _y : N.PlG k, Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k)))
  rw [Finset.prod_const, Finset.card_univ, N.card_PlG k]

theorem idem_integral (i : X.Tw) (b : Bool) :
    ∃ c : MonoidAlgebra (X.O i) (G0g N),
      MonoidAlgebra.map (algebraMap (X.O i) (FractionRing (X.O i))).toAddMonoidHom c =
        ((D.what₂.restRowsFiniteGroupCard : ℕ) : FractionRing (X.O i)) • Y.eAlg i b := by
  have : CharZero (FractionRing (X.O0 i)) := charZero_of_injective_ringHom (X.emb0 i).injective
  have : CharZero (X.O0 i) := (algebraMap (X.O0 i) (FractionRing (X.O0 i))).charZero
  have : CharZero (X.O i) := charZero_of_injective_ringHom (X.O_inj i)
  have : CharZero (FractionRing (X.O i)) :=
    charZero_of_injective_ringHom (IsFractionRing.injective (X.O i) (FractionRing (X.O i)))
  have hc := card_eq (N := N)
  have : Finite (G0g N) := Nat.finite_of_card_ne_zero (hc ▸ D.what₂.restRowsFiniteGroupCard_pos.ne')
  let : Fintype (G0g N) := Fintype.ofFinite _
  choose c hcc using GlobalTheory.T.exists_integral_card_mul_coeff_central_idempotent (G0g N) (X.O i) (FractionRing (X.O i)) (Y.eAlg i b) (Y.eAlg_idem i b)
    (Y.eAlg_central i b)
  refine ⟨MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm c), ?_⟩
  ext g
  rw [hc, Nat.card_eq_fintype_card]
  simp [hcc]

theorem admALG_of_commG : ∀ D : D7, CommG D → IntegralHeckeForms.GroupAlgebraIntegrality D.nexp := fun D h =>
  (GlobalTheory.TwistInputsTest.admissibleGoodIdempotent_iff_reduced D.nexp).2 fun i hi b => ⟨idem_integral D.nexp i b, h i hi b⟩

end GlobalTheory.IdemAlg
end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.ResSel

namespace GlobalTheory.ResSel.CoefMap

section General

variable {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  {M' : Type} [AddCommGroup M'] [Module R' M'] [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul R' M']
  (rho : Representation R Γ M) (rho' : Representation R' Γ M') (u : M →ₛₗ[σ] M') (hu : Continuous u)
  (he : ∀ g m, u (rho g m) = rho' g (u m))

def semilinearCoefficientMapCocycles : Z1 rho →ₛₗ[σ] Z1 rho' where
  toFun z := ⟨fun g => u (z.1 g), hu.comp z.2.1, fun g h => by
    beta_reduce
    rw [z.2.2, map_add (f := _), he]⟩
  map_add' z w := Subtype.ext (funext fun g => map_add u _ _)
  map_smul' c z := Subtype.ext (funext fun g => map_smulₛₗ u _ _)

def slH1 : H1 rho →ₛₗ[σ] H1 rho' :=
  Submodule.mapQ _ _ (semilinearCoefficientMapCocycles rho rho' u hu he) fun z hz => by
    obtain ⟨m, hm⟩ := (mem_coboundaries1 rho _).1 hz
    refine (mem_coboundaries1 _ _).2 ⟨u m, fun g => ?_⟩
    change u (z.1 g) = _
    rw [show z.1 g = _ from hm g, map_sub, he]

theorem res_slH1 {H : Type} [Group H] [TopologicalSpace H] (phi : H →* Γ) (hphi : Continuous phi) (x : H1 rho) :
    resH1 rho' phi hphi (slH1 rho rho' u hu he x) =
      slH1 (rho.comp phi) (rho'.comp phi) u hu (fun g m => he (phi g) m) (resH1 rho phi hphi x) := by
  induction x using Submodule.Quotient.induction_on with
  | H z => rfl

theorem slH1_ur (J : Subgroup Γ) (x : H1 rho) (hx : x ∈ H1ur rho J) :
    slH1 rho rho' u hu he x ∈ H1ur rho' J := by
  have h0 : resH1 rho J.subtype continuous_subtype_val x = 0 := hx
  exact (res_slH1 rho rho' u hu he J.subtype continuous_subtype_val x).trans
    ((congrArg _ h0).trans (map_zero _))

end General

section Coef

variable {O K K' : Type} [CommRing O] [CommRing K] [CommRing K'] [Algebra O K] [Algebra O K'] (f : K →ₐ[O] K') (r : ℕ)

def vecMap : (Fin r → K) →ₛₗ[(f : K →+* K')] (Fin r → K') where
  toFun m a := f (m a)
  map_add' m m' := funext fun a => map_add f _ _
  map_smul' c m := funext fun a => map_mul f _ _

theorem vecMap_repOn {Γ : Type} [Group Γ] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (g : Γ) (m : Fin r → K) :
    vecMap f r (repOn ρ (1 : Γ →* Kˣ) K g m) = repOn ρ (1 : Γ →* K'ˣ) K' g (vecMap f r m) := by
  funext a

  simp [vecMap, repOn, matAct, map_sum]

end Coef

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i))
  {K K' : Type} [CommRing K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K]
  [CommRing K'] [Algebra (X.O0 i) K'] [TopologicalSpace K'] [DiscreteTopology K'] (f : K →ₐ[X.O0 i] K')

theorem slH1_mem_bkOn (v : PlE D.host) (x : H1 ((repOn ρ (1 : GE N →* Kˣ) K).comp (DecV N v).subtype))
    (hx : x ∈ bkOn bkP i ρ (1 : GE N →* Kˣ) K v) :
    slH1 ((repOn ρ (1 : GE N →* Kˣ) K).comp (DecV N v).subtype) ((repOn ρ (1 : GE N →* K'ˣ) K').comp (DecV N v).subtype)
      (vecMap f r) continuous_of_discreteTopology (fun g m => vecMap_repOn f ρ g.1 m) x ∈
      bkOn bkP i ρ (1 : GE N →* K'ˣ) K' v := by
  unfold bkOn at hx ⊢
  split_ifs at hx ⊢ with hv
  · induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, c, y, b, hc, hy, hz, rfl⟩ := hx
      refine Submodule.subset_span ⟨semilinearCoefficientMapCocycles _ _ (vecMap f r) continuous_of_discreteTopology
        (fun g m => vecMap_repOn f ρ g.1 m) z, c, y, f b, hc, hy, fun g a => ?_, rfl⟩
      change f ((z : ↥(DecV N v) → Fin r → K) g a) = _
      rw [hz, smul_eq_mul, smul_eq_mul, map_mul, AlgHom.commutes]
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  · rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]

theorem slH1_mem_selOn (Q : Finset (PlE D.host)) (x : H1 (repOn ρ (1 : GE N →* Kˣ) K))
    (hx : x ∈ selOn bkP i ρ (1 : GE N →* Kˣ) K Q) :
    slH1 (repOn ρ (1 : GE N →* Kˣ) K) (repOn ρ (1 : GE N →* K'ˣ) K') (vecMap f r) continuous_of_discreteTopology
      (vecMap_repOn f ρ) x ∈ selOn bkP i ρ (1 : GE N →* K'ˣ) K' Q := by
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  refine (res_slH1 (repOn ρ (1 : GE N →* Kˣ) K) (repOn ρ (1 : GE N →* K'ˣ) K') (vecMap f r) continuous_of_discreteTopology
    (vecMap_repOn f ρ) (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x) ▸ ?_
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  split_ifs at hv ⊢ with h1 h2
  · exact slH1_mem_bkOn bkP i ρ f v _ hv
  · exact Submodule.mem_top
  · exact slH1_ur _ _ _ _ _ _ _ hv

theorem cl_mem_selOn_of_algHom (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N)
    (bkP : BKPh X) (i : X.Tw) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (K K' : Type)
    [Field K] [Algebra (X.O0 i) K] [TopologicalSpace K] [DiscreteTopology K]
    [Field K'] [Algebra (X.O0 i) K'] [TopologicalSpace K'] [DiscreteTopology K'] (f : K →ₐ[X.O0 i] K')
    (Q : Finset (PlE D.host)) (x : Z1 (red i K ρ)) (x' : Z1 (red i K' ρ)) (h : ∀ g a, x'.1 g a = f (x.1 g a))
    (hx : cl x ∈ selOn bkP i ρ (1 : GE N →* Kˣ) K Q) : cl x' ∈ selOn bkP i ρ (1 : GE N →* K'ˣ) K' Q := by
  have e : x' = semilinearCoefficientMapCocycles _ _ (vecMap f D.R.r) continuous_of_discreteTopology (vecMap_repOn f ρ) x :=
    Subtype.ext (funext fun g => funext fun a => h g a)
  rw [e]
  exact slH1_mem_selOn bkP i ρ f Q (cl x) hx

end GlobalTheory.ResSel.CoefMap

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published
  GlobalTheory.ResSel GlobalTheory.TwistDet

namespace GlobalTheory.ResSel.SmallSub

theorem exists_fix_roots {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {n : ℕ}
    (hn : n ≠ 0) : ∃ K : Subgroup (G F Ω), IsOpen (K : Set (G F Ω)) ∧ (∀ a b : G F Ω, a * b * a⁻¹ * b⁻¹ ∈ K) ∧
      ∀ g ∈ K, ∀ ζ : Ω, ζ ^ n = 1 → g ζ = ζ := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : NeZero n := ⟨hn⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n
  have hp : ∀ ζ : Ω, ζ ^ n = 1 → ∃ k : ℕ, ξ ^ k = ζ := fun ζ h => by
    obtain ⟨k, -, hk⟩ := hξ.eq_pow_of_pow_eq_one h
    exact ⟨k, hk⟩
  have hc : ∀ a b : G F Ω, a (b ξ) = b (a ξ) := fun a b => by
    obtain ⟨j, hj⟩ := hp (a ξ) (by rw [← map_pow, hξ.pow_eq_one, map_one])
    obtain ⟨k, hk⟩ := hp (b ξ) (by rw [← map_pow, hξ.pow_eq_one, map_one])
    conv_lhs => rw [← hk, map_pow, ← hj]
    conv_rhs => rw [← hj, map_pow, ← hk]
    rw [← pow_mul, ← pow_mul, mul_comm]
  refine ⟨MulAction.stabilizer (G F Ω) ξ, stabilizer_isOpen_of_isIntegral ξ, fun a b => ?_, fun g hg ζ h => ?_⟩
  · show a (b (a⁻¹ (b⁻¹ ξ))) = ξ
    rw [hc a⁻¹ b⁻¹, mul_inv_apply, mul_inv_apply]
  · obtain ⟨k, rfl⟩ := hp ζ h
    have : g ξ = ξ := hg
    rw [map_pow, this]

theorem normal_of_comm {Γ : Type} [Group Γ] {K : Subgroup Γ} (h : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ K) : K.Normal :=
  ⟨fun k hk g => by simpa using K.mul_mem (h g k) hk⟩

theorem comm_mem_ker {Γ A : Type} [Group Γ] [CommGroup A] (φ : Γ →* A) (a b : Γ) : a * b * a⁻¹ * b⁻¹ ∈ φ.ker := by
  simp [MonoidHom.mem_ker]

theorem isOpen_ideal {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (h : IsAdic (IsLocalRing.maximalIdeal O)) {I : Ideal O} (hI : I ≠ ⊥) : IsOpen (I : Set O) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
  have := (isAdic_iff.1 h).1 n
  rwa [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, ← hn] at this

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw)

theorem l_ne_zero : ((X.l i : ℕ) : X.O0 i) ≠ 0 := by
  intro h
  have : NeZero (X.l i ^ 1) := ⟨pow_ne_zero _ (X.lPrime i).out.ne_zero⟩
  have h1 := (X.zk_prim i 1).neZero'.out
  apply h1
  have := congrArg (phiK X i 1) h
  simpa using this

theorem l_mem : ((X.l i : ℕ) : X.O0 i) ∈ IsLocalRing.maximalIdeal (X.O0 i) := by
  intro h
  have h2 := h.map (algebraMap (X.O0 i) (X.O i))
  rw [map_natCast] at h2
  exact X.O_l i h2

theorem exists_eps : ∃ K : Subgroup (GE N), IsOpen (K : Set (GE N)) ∧ (∀ a b : GE N, a * b * a⁻¹ * b⁻¹ ∈ K) ∧
    ∀ g ∈ K, IsLocalRing.residue (X.O0 i) ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) = 1 := by
  refine ⟨((Units.map (IsLocalRing.residue (X.O0 i)).toMonoidHom).comp (eps0 X i)).ker, ?_, comm_mem_ker _,
    fun g hg => congrArg Units.val hg⟩
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  have hc : Continuous fun g : GE N => ‖((cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ) : ℤ_[X.l i]) - 1‖ :=
    ((Units.continuous_val.comp (continuous_cycZ D.host.E N.Om (X.l i))).sub continuous_const).norm
  refine Filter.mem_of_superset ((isOpen_lt hc (continuous_const (y := (1 : ℝ)))).mem_nhds (by simp)) fun g hg => ?_
  obtain ⟨c, hc⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 hg
  apply Units.ext
  change IsLocalRing.residue (X.O0 i) (algebraMap ℤ_[X.l i] (X.O0 i) (cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ)) = 1
  rw [sub_eq_iff_eq_add.1 hc, map_add (f := _), map_add (f := _), map_one, map_one, map_mul, map_natCast, map_mul,
    (IsLocalRing.residue_eq_zero_iff _).2 (l_mem X i), zero_mul, zero_add]

theorem not_mem_two {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (v : PlE D.host)
    (h1 : v ∈ placesOver D.host.E p) : v ∉ placesOver D.host.E q := fun h2 => by
  have hc : IsCoprime (p : 𝓞 D.host.E) (q : 𝓞 D.host.E) := ((Nat.coprime_primes hp hq).mpr hne).cast
  obtain ⟨a, b, hab⟩ := hc
  refine v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
  exact hab ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left a h1) (v.asIdeal.mul_mem_left b h2)

theorem pD_not_mem {v : PlE D.host} (hv : v ∈ X.pD i) :
    v ∉ placesOver D.host.E (X.l i) ∧ ∀ k, v ∉ placesOver D.host.E (D.host.g k) := by
  have hv' : v ∈ placesOver D.host.E (if X.l i = D.host.pde then D.host.pde' else D.host.pde) := by
    rw [← X.pD_eq i]; exact hv
  have hl : (X.l i).Prime := (X.lPrime i).out
  split_ifs at hv' with h
  · exact ⟨not_mem_two D.host.pde'_prime hl (h ▸ D.host.pde_ne.symm) v hv',
      fun k => not_mem_two D.host.pde'_prime (D.host.g_prime k) (D.host.pde_ne_g k).2 v hv'⟩
  · exact ⟨not_mem_two D.host.pde_prime hl (Ne.symm h) v hv',
      fun k => not_mem_two D.host.pde_prime (D.host.g_prime k) (D.host.pde_ne_g k).1 v hv'⟩

theorem exists_kerT (s : X.Sig i) {I : Ideal (X.O0 i)} (hI : I ≠ ⊥) : ∃ K : Subgroup (GE N), IsOpen (K : Set (GE N)) ∧
    K.Normal ∧ (∀ w, X.rhoS i s w = 1 → ∀ g, g * w * g⁻¹ * w⁻¹ ∈ K) ∧ ∀ g ∈ K, ∀ a b, (Tmat i s g - 1) a b ∈ I := by
  let φ : GE N →* GL (Fin D.R.r) (X.O0 i ⧸ I) := (Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I)).comp (Tgl i s)
  have hφ : ∀ g, g ∈ φ.ker ↔ ∀ a b, (Tmat i s g - 1) a b ∈ I := by
    intro g
    rw [MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff, ← Tgl_coe]
    refine forall₂_congr fun a b => ?_
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq]
    have : ((1 : GL (Fin D.R.r) (X.O0 i ⧸ I)) : Matrix _ _ (X.O0 i ⧸ I)) a b =
        Ideal.Quotient.mk I ((1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) a b) := by
      rw [Units.val_one, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [this]
    rfl
  refine ⟨φ.ker, ?_, inferInstance, fun w hw g => ?_, fun g hg => (hφ g).1 hg⟩
  · have h1 : Continuous fun g : GE N => (((chiS i s g)⁻¹ : (X.O0 i)ˣ) : X.O0 i) := by
      simp only [← map_inv]
      exact (X.twistCharacterFamily_continuous i _ _).comp continuous_inv
    have hc : Continuous (Tmat i s) := h1.smul (X.rhoS_cont i s)
    have e : (φ.ker : Set (GE N)) = ⋂ a, ⋂ b, (fun g => (Tmat i s g - 1) a b) ⁻¹' (I : Set (X.O0 i)) := by
      ext g
      simp only [SetLike.mem_coe, hφ, Set.mem_iInter, Set.mem_preimage]
    rw [e]
    exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b =>
      (isOpen_ideal (X.twistBaseCoefficientRing_isAdic i) hI).preimage ((hc.sub continuous_const).matrix_elem a b)
  · have h1 : Tgl i s w = scalGL D.R.r (chiS i s w)⁻¹ := by
      change scalGL _ _ * X.rhoS i s w = _
      rw [hw, mul_one]
    have h2 : Tgl i s (g * w * g⁻¹ * w⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1, ← scalGL_comm]
      group
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, h2, map_one]

theorem exists_small : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X)
    (i : X.Tw) (T : Set (X.Sig i)), (∀ s ∈ T, GalHyp bkP i s) → ∀ z, IsTameInertiaElementAtTwistPrime X i z → ∀ (M : ℕ) (H : Subgroup (GE N)),
    IsOpen (H : Set (GE N)) → H.Normal →
    (∀ v ∈ X.pD i, ∀ A : ValuationSubring N.Om, IsPlaceOver A v → Ine (F := D.host.E) A ≤ H) →
    ∃ L : Subgroup (GE N), IsOpen (L : Set (GE N)) ∧ L.Normal ∧ L ≤ H ∧ (∀ s ∈ T, Small i s L z) ∧
      (∀ g ∈ L, ∀ ζ : N.Om, ζ ^ (2 * X.l i ^ M) = 1 → g ζ = ζ) ∧ ∀ s ∈ T, ∀ g ∈ L, ∀ a b,
        (Tmat i s g - 1) a b ∈ Ideal.span {(X.l i : X.O0 i) ^ nu X i} * IsLocalRing.maximalIdeal (X.O0 i) := by
  intro D N X bkP i T hT z hz M H hH hN hI
  obtain ⟨K₁, o₁, c₁, f₁⟩ := exists_fix_roots (F := D.host.E) (Ω := N.Om) (n := 2 * X.l i ^ M)
    (mul_ne_zero two_ne_zero (pow_ne_zero _ (X.lPrime i).out.ne_zero))
  obtain ⟨K₂, o₂, c₂, f₂⟩ := exists_eps X i
  have hne : Ideal.span {(X.l i : X.O0 i) ^ nu X i} * IsLocalRing.maximalIdeal (X.O0 i) ≠ ⊥ :=
    mul_ne_zero (fun h => pow_ne_zero _ (l_ne_zero X i) (Ideal.span_singleton_eq_bot.1 h)) (IsDiscreteValuationRing.not_a_field _)
  choose K o n c f using fun s => exists_kerT X i s hne
  have := normal_of_comm c₁
  have := normal_of_comm c₂
  let H₀ : Subgroup (GE N) := H ⊓ (K₁ ⊓ (K₂ ⊓ ⨅ s : T, K s))
  have hK : (⨅ s : T, K s).Normal := Subgroup.normal_iInf_normal fun s => n s
  have hn₀ : H₀.Normal := inferInstance
  have ho₀ : IsOpen (H₀ : Set (GE N)) := by
    refine hH.inter (o₁.inter (o₂.inter ?_))
    change IsOpen ((⨅ s : T, K s : Subgroup (GE N)) : Set (GE N))
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun s => o s
  have hw : ∀ v ∈ X.pD i, ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ w ∈ Ine (F := D.host.E) A,
      ∀ g, g * w * g⁻¹ * w⁻¹ ∈ H₀ := fun v hv A hA w hw g =>
    ⟨H.mul_mem (hN.conj_mem _ (hI v hv A hA hw) g) (H.inv_mem (hI v hv A hA hw)), c₁ _ _, c₂ _ _,
      Subgroup.mem_iInf.2 fun s => c s w ((hT s s.2).1.1 v (pD_not_mem X i hv).1 (pD_not_mem X i hv).2 A hA w hw) g⟩
  have hL : IsOpen ((H₀ ⊓ H₀.comap (cConj X) : Subgroup (GE N)) : Set (GE N)) := ho₀.inter (isOpen_comap_cConj X ho₀)
  have hf : ∀ s ∈ T, ∀ g ∈ H₀ ⊓ H₀.comap (cConj X), ∀ a b,
      (Tmat i s g - 1) a b ∈ Ideal.span {(X.l i : X.O0 i) ^ nu X i} * IsLocalRing.maximalIdeal (X.O0 i) :=
    fun s hs g hg => f s g (Subgroup.mem_iInf.1 hg.1.2.2.2 ⟨s, hs⟩)
  refine ⟨H₀ ⊓ H₀.comap (cConj X), hL, inferInstance, fun g hg => hg.1.1,
    fun s hs => ⟨hL, inferInstance, fun g g' hg => ?_, fun g => ?_, fun g hg => ⟨?_, f₂ g hg.1.2.2.1⟩⟩,
    fun g hg => f₁ g hg.1.2.1, hf⟩
  · obtain rfl : g' = cConj X g := AlgEquiv.ext hg
    simp only [Subgroup.mem_inf, Subgroup.mem_comap, cConj_cConj]
    exact and_comm
  · obtain ⟨v, hv, A, hA, hzA, -⟩ := hz
    refine ⟨hw v hv A hA z hzA g, ?_⟩
    obtain ⟨v', hv'⟩ := exists_isConjPl v
    have hv'' : v' ∈ X.pD i := by
      rw [← Finset.mem_coe, X.pD_eq] at hv ⊢
      exact mem_placesOver_conj hv' hv
    have := hw v' hv'' _ (isPlaceOver_moveVal_cc X hv' hA) _ (cConj_mem_ine X hzA) (cConj X g)
    change cConj X _ ∈ H₀
    rwa [map_mul, map_mul, map_mul, map_inv, map_inv]
  · ext a b
    have h0 : (Tmat i s g - 1) a b ∈ IsLocalRing.maximalIdeal (X.O0 i) := Ideal.mul_le_right (hf s hs g hg a b)
    have := (IsLocalRing.residue_eq_zero_iff _).2 h0
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    rw [Matrix.map_apply, this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

end GlobalTheory.ResSel.SmallSub

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.ResConjTriv

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

theorem continuous_cConj : Continuous (GlobalTheory.TwistDet.cConj X) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨L, hL, hLs⟩ := (krullTopology_mem_nhds_one_iff D.host.E N.Om s).1 hs
  have h := GlobalTheory.TwistDet.isOpen_comap_cConj X (H := L.fixingSubgroup) (IntermediateField.fixingSubgroup_isOpen L)
  rw [Filter.mem_map]
  exact Filter.mem_of_superset (h.mem_nhds (Subgroup.one_mem _)) fun g hg => hLs hg

theorem cycZ_cConj (l : ℕ) [Fact l.Prime] (g : GE N) :
    cycZ (F := D.host.E) (Ω := N.Om) l (GlobalTheory.TwistDet.cConj X g) = cycZ (F := D.host.E) (Ω := N.Om) l g := by
  have e : (GlobalTheory.TwistDet.cConj X g).toRingEquiv = X.cc * g.toRingEquiv * X.cc⁻¹ := by
    ext x; rfl
  change cyclotomicCharacter N.Om l (GlobalTheory.TwistDet.cConj X g).toRingEquiv = cyclotomicCharacter N.Om l g.toRingEquiv
  rw [e, map_mul, map_mul, map_inv, mul_inv_cancel_comm]

theorem auxiliaryCharacter_complexConj_invariant (i : X.Tw) (g : GE N) : eps0 X i (GlobalTheory.TwistDet.cConj X g) = eps0 X i g := by
  simp only [eps0, MonoidHom.comp_apply, cycZ_cConj]

theorem resTriv_cConj (i : X.Tw) (s : X.Sig i) (hS : SelfDual i s) (g : GE N) (hg : ResTriv i s g) :
    ResTriv i s (GlobalTheory.TwistDet.cConj X g) := by
  obtain ⟨A, hA⟩ := hS
  obtain ⟨h1, h2⟩ := hg
  have h3 := hA g _ (GlobalTheory.TwistDet.cConj_apply X g)
  refine ⟨?_, by rw [auxiliaryCharacter_complexConj_invariant, h2]⟩
  set φ := IsLocalRing.residue (X.O0 i) with hφ
  have hsm : ∀ (c : X.O0 i) (M : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)), φ c = 1 → (c • M).map φ = M.map φ := by
    intro c M hc
    ext a b
    simp [hc]
  have h4 := congrArg (fun M => M.map φ) h3
  simp only [Tdual] at h4
  rw [hsm _ _ (by rw [auxiliaryCharacter_complexConj_invariant, h2]), Matrix.map_mul, Matrix.map_mul, hsm _ _ (by rw [map_pow, h2, one_pow]), h1,
    mul_one, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.transpose_map,
    Matrix.transpose_eq_one] at h4
  have hu : IsUnit (Tmat i s (GlobalTheory.TwistDet.cConj X g)).det := by
    rw [← Tgl_coe]
    exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
  have h5 := congrArg (fun M => M.map φ) (Matrix.mul_nonsing_inv _ hu)
  rwa [Matrix.map_mul, h4, mul_one, Matrix.map_one _ (map_zero φ) (map_one φ)] at h5

theorem continuous_cConj_and_resTriv : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N), Continuous (GlobalTheory.TwistDet.cConj X) ∧ ∀ (i : X.Tw) (s : X.Sig i), SelfDual i s → ∀ g : GE N, ResTriv i s g → ResTriv i s (GlobalTheory.TwistDet.cConj X g) :=
  fun _ _ X => ⟨continuous_cConj X, resTriv_cConj X⟩

end GlobalTheory.ResConjTriv
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.breuilKisin_zeta_fine_bound_second_basis : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), 1 ≤ η → η < H → 14 * H < l → ∀ y ∈ D.Y', ∃ p ∈ D.L, ∃ f ∈ D.FilMM (10 * H), D.zeta y = (l : K) ^ (l - 14 * H) • p + ((l : K) ^ (3 * H))⁻¹ • f := by
  first | exact @GlobalTheory.BK.zeta_Y'_fine_bound | exact GlobalTheory.BK.zeta_Y'_fine_bound | (intros; apply GlobalTheory.BK.zeta_Y'_fine_bound <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem _root_.GlobalTheory.T.wachInclusionLayer_io_commutes_frobenius_galois : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R) (S : Type) [CommRing S] (f f' : RA LL →+* S), ((∀ o w, f' (o ⊗ₜ[ℤ_[l]] w) = f (o ⊗ₜ[ℤ_[l]] WittVector.frobenius w)) → ∀ a, f (I.io (letφ R.φ₀ a)) = f' (I.io a)) ∧ ∀ g : ↥(GK K), (∀ o w, f' (o ⊗ₜ[ℤ_[l]] w) = f (o ⊗ₜ[ℤ_[l]] AI.actW (g : GQ l) w)) → ∀ a, f (I.io (letγ (R.γ₀ (Γ.resΓ g)) a)) = f' (I.io a) := by
  first | exact @GlobalTheory.HWL.IoComm.main | exact GlobalTheory.HWL.IoComm.main | (intros; apply GlobalTheory.HWL.IoComm.main <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem _root_.GlobalTheory.T.wachInclusion_injective_saturated_inter : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → Function.Injective I.ioE ∧ (∀ x : R.EE, IsUnit (I.ioE x) → IsUnit x) ∧ (∀ (x : R.EE) (y : RW LL), I.ioE x = ((l : ℕ) : RW LL) * y → ∃ x', x = ((l : ℕ) : R.EE) * x') ∧ ∀ x : R.EE, (∃ y, inclR LL y = I.ioE x) → ∃ a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)), algebraMap _ R.EE a = x := by
  first | exact @GlobalTheory.IoInj.ioE_injective_saturated_inter | exact GlobalTheory.IoInj.ioE_injective_saturated_inter | (intros; apply GlobalTheory.IoInj.ioE_injective_saturated_inter <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

theorem _root_.GlobalTheory.T.lam0_isUnitary_and_trivOnF : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m), (Z.lam0 l j a).IsUnitary ∧ TrivOnF (Z.lam0 l j a) := by
  first | exact @GlobalTheory.LamTie.toricLam0_unitary_trivOnMaxRealSubfield | exact GlobalTheory.LamTie.toricLam0_unitary_trivOnMaxRealSubfield | (intros; apply GlobalTheory.LamTie.toricLam0_unitary_trivOnMaxRealSubfield <;> assumption)
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

theorem _root_.GlobalTheory.T.conductor_exponent_at_places : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (q0 : ℕ) (w0 : HeightOneSpectrum (𝓞 H.E)), PlacesOk H q0 w0 → ∀ w : HeightOneSpectrum (𝓞 H.E), (Over4 H w → expIn (cond0 H w0) (below w) = 2) ∧ (below w = below w0 → ¬ Over4 H w ∧ expIn (cond0 H w0) (below w) = 1) ∧ (¬ Over4 H w → below w ≠ below w0 → expIn (cond0 H w0) (below w) = 0) := by
  first | exact @GlobalTheory.LamTie.expIn_cond0 | exact GlobalTheory.LamTie.expIn_cond0 | (intros; apply GlobalTheory.LamTie.expIn_cond0 <;> assumption)
end
