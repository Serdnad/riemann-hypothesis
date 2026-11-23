module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltWittEqZeroOfPrimeMulEqZero
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle268
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle300
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL.IoComm

variable {l : ℕ} [Fact l.Prime]

theorem transfer {Z O A W S : Type} [CommRing Z] [CommRing O] [CommRing A] [CommRing W] [CommRing S]
    [Algebra Z O] [Algebra Z A] [Algebra Z W] (j : A →ₐ[Z] W)
    (hj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id O O) j))
    (ψ : A →ₐ[Z] A) (Ψ : W →ₐ[Z] W) (h : ∀ w, Ψ (j w) = j (ψ w)) (f f' : O ⊗[Z] A →+* S)
    (hf : ∀ o w, f' (o ⊗ₜ[Z] w) = f (o ⊗ₜ[Z] ψ w)) (x y : O ⊗[Z] A)
    (hxy : Algebra.TensorProduct.map (AlgHom.id O O) j y =
      Algebra.TensorProduct.map (AlgHom.id O O) Ψ (Algebra.TensorProduct.map (AlgHom.id O O) j x)) :
    f y = f' x := by
  let Φ : O ⊗[Z] A →ₐ[O] O ⊗[Z] A := Algebra.TensorProduct.map (AlgHom.id _ _) ψ
  have h1 : ∀ z : O ⊗[Z] A, Algebra.TensorProduct.map (AlgHom.id O O) j (Φ z) =
      Algebra.TensorProduct.map (AlgHom.id O O) Ψ (Algebra.TensorProduct.map (AlgHom.id O O) j z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul o w =>
      simp only [Φ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, h]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have h2 : ∀ z : O ⊗[Z] A, f (Φ z) = f' z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul o w =>
      rw [hf]
      simp only [Φ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have h3 : y = Φ x := hj (hxy.trans (h1 x).symm)
  rw [h3, h2]

def frobA (l : ℕ) [Fact l.Prime] : Ainf l →ₐ[ℤ_[l]] Ainf l where
  toRingHom := WittVector.map (frobenius (OCb l) l)
  commutes' := fun x => map_zlW l _ x

theorem frobA_apply (w : Ainf l) : frobA l w = WittVector.frobenius w := by
  rw [WittVector.frobenius_eq_map_frobenius]
  rfl

theorem frobW_inclWA (w : Ainf l) : frobW l (inclWA l w) = inclWA l (frobA l w) := by
  ext n
  change frobenius (Cb l) l (algebraMap (OCb l) (Cb l) (w.coeff n)) =
    algebraMap (OCb l) (Cb l) (frobenius (OCb l) l (w.coeff n))
  rw [frobenius_def, frobenius_def, map_pow]

theorem act_inclWA {P : LocPrime l} (AI : LocAinf l P) (g : GQ l) (w : Ainf l) :
    (AI.actWCbHom g).toAlgHom (inclWA l w) = inclWA l ((AI.actWHom g).toAlgHom w) := by
  ext n
  exact autCb_alg l (AI.actT g) (w.coeff n)

section

variable {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l} {Γ : GamS P K s LL}
  {R : WSer Γ} (I : IoS AI R)

theorem incl_io_φ (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) :
    inclR LL (I.io (letφ R.φ₀ a)) = φRW LL (inclR LL (I.io a)) :=
  ((I.ioE_ext _).symm.trans (congrArg I.ioE (R.φE_ext a).symm)).trans
    ((I.ioE_φ _).trans (congrArg (φRW LL) (I.ioE_ext a)))

theorem incl_io_γ (g : ↥(GK K)) (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) :
    inclR LL (I.io (letγ (R.γ₀ (Γ.resΓ g)) a)) = AI.gRW LL (g : GQ l) (inclR LL (I.io a)) :=
  ((I.ioE_ext _).symm.trans (congrArg I.ioE (R.γE_ext _ a).symm)).trans
    ((I.ioE_γ g _).trans (congrArg (AI.gRW LL (g : GQ l)) (I.ioE_ext a)))

end

theorem transfer_φ (LL : FinExt l) {S : Type} [CommRing S] (f f' : RA LL →+* S)
    (hf : ∀ o w, f' (o ⊗ₜ[ℤ_[l]] w) = f (o ⊗ₜ[ℤ_[l]] WittVector.frobenius w)) (x y : RA LL)
    (hxy : inclR LL y = φRW LL (inclR LL x)) : f y = f' x :=
  transfer (inclWA l) (GlobalTheory.HWL.TensorWitt.main l LL).2.2.1 (frobA l) (frobW l) frobW_inclWA f f'
    (fun o w => by rw [frobA_apply, hf]) x y hxy

theorem transfer_γ {P : LocPrime l} (AI : LocAinf l P) (g : GQ l) (LL : FinExt l) {S : Type} [CommRing S]
    (f f' : RA LL →+* S)
    (hf : ∀ o w, f' (o ⊗ₜ[ℤ_[l]] w) = f (o ⊗ₜ[ℤ_[l]] AI.actW g w)) (x y : RA LL)
    (hxy : inclR LL y = AI.gRW LL g (inclR LL x)) : f y = f' x :=
  transfer (inclWA l) (GlobalTheory.HWL.TensorWitt.main l LL).2.2.1 (AI.actWHom g).toAlgHom
    (AI.actWCbHom g).toAlgHom (act_inclWA AI g) f f' (fun o w => hf o w) x y hxy

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R) (S : Type) [CommRing S] (f f' : RA LL →+* S), ((∀ o w, f' (o ⊗ₜ[ℤ_[l]] w) = f (o ⊗ₜ[ℤ_[l]] WittVector.frobenius w)) → ∀ a, f (I.io (letφ R.φ₀ a)) = f' (I.io a)) ∧ ∀ g : ↥(GK K), (∀ o w, f' (o ⊗ₜ[ℤ_[l]] w) = f (o ⊗ₜ[ℤ_[l]] AI.actW (g : GQ l) w)) → ∀ a, f (I.io (letγ (R.γ₀ (Γ.resΓ g)) a)) = f' (I.io a) := by
  intro l _ P AI K s LL Γ R I S _ f f'
  exact ⟨fun hf a => transfer_φ LL f f' hf _ _ (incl_io_φ I a),
    fun g hf a => transfer_γ AI (g : GQ l) LL f f' hf _ _ (incl_io_γ I g a)⟩

end GlobalTheory.HWL.IoComm
end
end

section

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie.InfType

theorem inf_eq_one {L : Type} [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] {χ : Formalism.L2.Host.HChar L} {n : ℕ} (hn : 0 < n)
    (h : χ.OrderDvd n) (k : Lˣ) : χ.inf k = 1 := by
  have hx : ∀ x, (χ.1 x) ^ n = 1 := fun x => congrArg (fun ξ : Formalism.L2.Host.HChar L => ξ.1 x) h
  have hw : ∀ (w : InfinitePlace L) (y : (w.Completion)ˣ), χ.locInf w y = 1 := by
    intro w y
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e (y : w.Completion)) hn
    have hz' : (e.symm z) ^ n = y := by rw [← map_pow, hz]; simp
    have hz0 : e.symm z ≠ 0 := by
      intro h0; rw [h0, zero_pow hn.ne'] at hz'; exact y.ne_zero hz'.symm
    have : y = (Units.mk0 _ hz0) ^ n := Units.ext (by simp [hz'])
    rw [this, map_pow]
    exact hx _
  show χ.1 (Formalism.L2.Host.infDiag k) = 1
  unfold Formalism.L2.Host.infDiag
  classical
  have hp : ∀ s : Finset (InfinitePlace L),
      (∏ w ∈ s, (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w).comp (atInf w)) k =
        ∏ w ∈ s, ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w (atInf w k) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert w s hws ih => simp [hws, ih, MonoidHom.mul_apply]
  rw [hp, map_prod]
  exact Finset.prod_eq_one fun w _ => hw w _

theorem conj_div_norm {z : ℂ} (hz : z ≠ 0) :
    starRingEnd ℂ z / ((‖starRingEnd ℂ z‖ : ℝ) : ℂ) = (z / ((‖z‖ : ℝ) : ℂ))⁻¹ := by
  have h1 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
  rw [Complex.norm_conj, inv_div, div_eq_div_iff h1 hz, ← sq, ← Complex.mul_conj', mul_comm]

theorem delAt_inf {D : D7} (C : CharFrame D) (l : ℕ) (k : D.host.Eˣ) : (C.delAt l).inf k = 1 := by
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  unfold CharFrame.delAt
  split_ifs
  · obtain ⟨n, hn, h⟩ := C.isDel'.fin
    exact inf_eq_one hn h k
  · obtain ⟨n, hn, h⟩ := C.isDel.fin
    exact inf_eq_one hn h k

theorem toricLam0_hasInfinityType_conjRatio (D : D7) (Z : LamDat D) (hZ : Z.Ok) (l : ℕ) (j a : Fin D.R.m) (s : ℕ)
    (hs : (s : ℤ) ≤ (BlochKatoReduction.Gen.NFun D.R : ℤ) + 1) :
    (∀ g, 1 ≤ Z.kap j a s g) ∧
      GlobalTheory.CMVal.HasInf (Z.lam0 l j a) (phi D.host) (fun g => (Z.kap j a s g : ℤ) + s) := by
  have he : ∀ g, ∃ z : ℤ, eExp D j g = z := fun g => (D.hc _).e_int j
  choose e he using he
  have hpos : ∀ g, 1 ≤ e g + Z.c a g - s := fun g => by
    have h := hZ.big j a g
    rw [he] at h
    have h' : (BlochKatoReduction.Gen.NFun D.R : ℤ) + 1 < e g + Z.c a g := by exact_mod_cast h
    omega
  have hk : ∀ g, (Z.kap j a s g : ℤ) = e g + Z.c a g - s := fun g => by
    unfold LamDat.kap
    rw [he, Int.floor_intCast]
    exact Int.toNat_of_nonneg (by have := hpos g; omega)
  refine ⟨fun g => by have := hk g; have := hpos g; omega, fun k => ?_⟩
  obtain ⟨n, hn, h1⟩ := (Z.C.isMu0 j).inf
  obtain ⟨n', hn', h2⟩ := (hZ.aux a).inf
  unfold LamDat.lam0
  rw [HChar.inf_mul, HChar.inf_mul, HChar.inf_inv, delAt_inf, mul_one, Units.val_mul, Units.val_inv_eq_inv_val, h1 k, h2 k,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun g _ => ?_
  have hz : embPsi D.host g (k : D.host.E) ≠ 0 := by simp
  have hu : embPsi D.host g (k : D.host.E) / ((‖embPsi D.host g (k : D.host.E)‖ : ℝ) : ℂ) ≠ 0 :=
    div_ne_zero hz (by exact_mod_cast norm_ne_zero_iff.2 hz)
  have e1 : n g = 2 * -(e g) := by
    have := hn g
    simp only [he] at this
    exact_mod_cast this
  have e2 : n' g = 2 * Z.c a g := by
    have := hn' g
    beta_reduce at this
    exact_mod_cast this
  have e3 : phi D.host g (k : D.host.E) = starRingEnd ℂ (embPsi D.host g (k : D.host.E)) := rfl
  rw [e3, conj_div_norm hz, inv_zpow', ← zpow_neg, ← zpow_add₀ hu, e1, e2]
  congr 1
  beta_reduce
  rw [hk]
  ring

end GlobalTheory.LamTie.InfType
end
end

section

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTieWeak

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem isThEmpty_of_isThOf {i : X.Tw} {ι : ℂ →+* Kbar X i} {lam : X.abelian₂ i} {I : Type} [Fintype I] {φ : I → D.host.E →+* ℂ}
    {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF D.host.E)} {χ : Formalism.L2.Host.HChar D.host.E}
    (h : IsThOf X i ι lam φ s κ 𝔣 χ) : IsThEmpty X i ι lam φ s κ 𝔣 χ := by
  classical
  obtain ⟨u, hu, hth⟩ := h
  have hQ : BlochKatoReduction.Gen.QOk X i ∅ :=
    ⟨fun _ h => absurd h (Finset.notMem_empty _), Finset.disjoint_empty_left _, fun _ h => absurd h (Finset.notMem_empty _)⟩
  obtain ⟨hfin, π, T, -, hT, hδ⟩ := hth ∅ hQ
  have he : belowSet (∅ : Finset (HeightOneSpectrum (𝓞 D.host.E))) = ∅ := Finset.image_empty _
  have hc : condQ 𝔣 (belowSet (∅ : Finset (HeightOneSpectrum (𝓞 D.host.E)))) = 𝔣 := by
    rw [he]; simp [condQ]
  have := Fintype.ofFinite (PicO (condQ 𝔣 (belowSet (∅ : Finset (HeightOneSpectrum (𝓞 D.host.E))))))
  have t : IsToricSum φ s κ (condQ 𝔣 (belowSet (∅ : Finset (HeightOneSpectrum (𝓞 D.host.E))))) χ (∑ q, T q) :=
    (isToricSum_iff _ _ _ _ _ _).2 ⟨hfin, T, hT, (finsum_eq_sum_of_fintype _).symm⟩
  have key : ∀ z : ℂ, IsToricSum φ s κ (condQ 𝔣 (belowSet (∅ : Finset (HeightOneSpectrum (𝓞 D.host.E))))) χ z →
      IsToricSum φ s κ 𝔣 χ z := by
    rw [hc]; exact fun _ hz => hz
  refine ⟨u, ∑ q, T q, hu, key _ t, ?_⟩

  rw [map_sum, Finset.sum_congr rfl fun δ _ => hδ δ, ← Finset.mul_sum, ← map_sum,
  ← Finset.sum_fiberwise Finset.univ (fun q => π q⁻¹)]
  congr 2
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [show {q | π q⁻¹ = δ} = ↑(Finset.univ.filter fun q => π q⁻¹ = δ) by ext; simp, finsum_mem_coe_finset]

theorem isLamTie0_of_isLamTie : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (Z : LamDat D),
    IsLamTie X Z → IsLamTie0 X Z := by
  intro D N X Z h i hi lam
  obtain ⟨-, ι, -, hι⟩ := h i hi
  obtain ⟨j, a, s, hl, ht⟩ := hι lam
  exact ⟨_, j, a, s, hl.2.1, isThEmpty_of_isThOf ht⟩

end GlobalTheory.LamTieWeak
end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie.ExpCond

theorem not_mem_sq_of_not_dvd_discr {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr E)
    (w : HeightOneSpectrum (𝓞 E)) (hv : (p : 𝓞 E) ∈ w.asIdeal) : (p : 𝓞 E) ∉ w.asIdeal ^ 2 := by
  intro h2
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hvZ : ((p : ℤ) : 𝓞 E) ∈ w.asIdeal := by simpa using hv
  have hun : Algebra.IsUnramifiedAt ℤ w.asIdeal :=
    (NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E) hpZ).mp hd w.asIdeal w.isPrime hvZ
  have hunder : w.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
    symm
    refine (PrincipalIdealRing.isMaximal_of_irreducible hpZ.irreducible).eq_of_le
      (Ideal.IsPrime.under ℤ w.asIdeal).ne_top ?_
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_comap.mpr (by simpa using hv)
  let := Localization.AtPrime.algebraOfLiesOver (w.asIdeal.under ℤ) w.asIdeal
  have hloc := ((Algebra.isUnramifiedAt_iff_map_eq ℤ (w.asIdeal.under ℤ) w.asIdeal).mp hun).2
  have h1 := (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff w.ne_bot Ideal.map_comap_le).mpr hloc
  refine (Ideal.ramificationIdx'_ne_one_iff Ideal.map_comap_le).mpr ?_ h1
  have hunder' : Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal = Ideal.span {(p : ℤ)} := hunder
  rw [hunder', Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
  simpa using h2

variable {E : Type} [Field E] [NumberField E]

theorem mem_below (w : HeightOneSpectrum (𝓞 E)) (p : ℕ) : (p : OF E) ∈ (below w).asIdeal ↔ (p : 𝓞 E) ∈ w.asIdeal := by
  show (p : OF E) ∈ Ideal.comap (algebraMap (OF E) (𝓞 E)) w.asIdeal ↔ _
  rw [Ideal.mem_comap, map_natCast]

theorem emult_zero (w : HeightOneSpectrum (𝓞 E)) {p : ℕ} (h : (p : 𝓞 E) ∉ w.asIdeal) :
    emultiplicity (below w).asIdeal (Ideal.span {(p : OF E)}) = 0 := by
  rw [emultiplicity_eq_zero, Ideal.dvd_span_singleton, mem_below]
  exact h

theorem emult_one (w : HeightOneSpectrum (𝓞 E)) {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr E) (h : (p : 𝓞 E) ∈ w.asIdeal) :
    emultiplicity (below w).asIdeal (Ideal.span {(p : OF E)}) = 1 := by
  have hle : Ideal.map (algebraMap (OF E) (𝓞 E)) (below w).asIdeal ≤ w.asIdeal :=
    Ideal.map_le_iff_le_comap.mpr (fun x hx => hx)
  have hdvd : (below w).asIdeal ^ 1 ∣ Ideal.span {(p : OF E)} := by
    rw [pow_one, Ideal.dvd_span_singleton, mem_below]
    exact h
  have hndvd : ¬ (below w).asIdeal ^ (1 + 1) ∣ Ideal.span {(p : OF E)} := by
    intro h2
    rw [Ideal.dvd_span_singleton] at h2
    have hm := Ideal.mem_map_of_mem (algebraMap (OF E) (𝓞 E)) h2
    rw [Ideal.map_pow, map_natCast] at hm
    have hsq : (Ideal.map (algebraMap (OF E) (𝓞 E)) (below w).asIdeal) ^ (1 + 1) ≤ w.asIdeal ^ 2 := by
      rw [show (1 + 1 : ℕ) = 2 from rfl, pow_two, pow_two]
      exact Ideal.mul_mono hle hle
    exact not_mem_sq_of_not_dvd_discr hp hd w h (hsq hm)
  have := (emultiplicity_eq_coe (n := 1)).mpr ⟨hdvd, hndvd⟩
  simpa using this

theorem not_mem_of_ne (w : HeightOneSpectrum (𝓞 E)) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (h : (p : 𝓞 E) ∈ w.asIdeal) : (q : 𝓞 E) ∉ w.asIdeal := by
  intro hq'
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hne)
  obtain ⟨u, v, huv⟩ := hc
  have e : (u : 𝓞 E) * (p : 𝓞 E) + (v : 𝓞 E) * (q : 𝓞 E) = 1 := by
    have := congrArg (Int.cast : ℤ → 𝓞 E) huv
    push_cast at this
    exact this
  have h1 : (1 : 𝓞 E) ∈ w.asIdeal := by
    rw [← e]
    exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ h) (w.asIdeal.mul_mem_left _ hq')
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem emult_cond (v v0 : HeightOneSpectrum (OF E)) (a b c d : ℕ) :
    emultiplicity v.asIdeal (Ideal.span {((a * b * c * d : ℕ) : OF E)} ^ 2 * v0.asIdeal) =
      2 * (emultiplicity v.asIdeal (Ideal.span {(a : OF E)}) + emultiplicity v.asIdeal (Ideal.span {(b : OF E)}) +
        emultiplicity v.asIdeal (Ideal.span {(c : OF E)}) + emultiplicity v.asIdeal (Ideal.span {(d : OF E)})) +
        emultiplicity v.asIdeal v0.asIdeal := by
  have hv := v.prime
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton,
    ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
    emultiplicity_mul hv, emultiplicity_pow hv, emultiplicity_mul hv, emultiplicity_mul hv,
    emultiplicity_mul hv]
  push_cast
  ring

theorem emult_ne {v v0 : HeightOneSpectrum (OF E)} (h : v ≠ v0) : emultiplicity v.asIdeal v0.asIdeal = 0 := by
  rw [emultiplicity_eq_zero, Ideal.dvd_iff_le]
  intro hle
  apply h
  exact HeightOneSpectrum.ext ((v0.isMaximal.eq_of_le v.isPrime.ne_top hle).symm)

theorem emult_self (v : HeightOneSpectrum (OF E)) : emultiplicity v.asIdeal v.asIdeal = 1 := by
  simpa using emultiplicity_pow_self_of_prime v.prime 1

end GlobalTheory.LamTie.ExpCond

namespace GlobalTheory.LamTie

open ExpCond

theorem expIn_cond0 : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (q0 : ℕ) (w0 : HeightOneSpectrum (𝓞 H.E)), PlacesOk H q0 w0 →
    ∀ w : HeightOneSpectrum (𝓞 H.E), (Over4 H w → expIn (cond0 H w0) (below w) = 2) ∧
      (below w = below w0 → ¬ Over4 H w ∧ expIn (cond0 H w0) (below w) = 1) ∧
      (¬ Over4 H w → below w ≠ below w0 → expIn (cond0 H w0) (below w) = 0) := by
  intro R H q0 w0 hP w
  obtain ⟨hw0, hdist, hspl⟩ := hP
  have hq0 : (q0 : 𝓞 H.E) ∈ w0.asIdeal := hw0
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, not_or, or_false] at hdist
  have pr : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], p.Prime := fun p hp => (hspl p hp).1
  have dc : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], ¬ (p : ℤ) ∣ discr H.E := fun p hp => (hspl p hp).2.2.1
  have uniq : ∀ x ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], ∀ y ∈ [H.g 0, H.g 1, H.pde, H.pde', q0],
      (x : 𝓞 H.E) ∈ w.asIdeal → (y : 𝓞 H.E) ∈ w.asIdeal → x = y := by
    intro x hx y hy mx my
    by_contra hxy
    exact not_mem_of_ne w (pr x hx) (pr y hy) hxy mx my
  have key : emultiplicity (below w).asIdeal (cond0 H w0) =
      2 * (emultiplicity (below w).asIdeal (Ideal.span {(H.g 0 : OF H.E)}) +
        emultiplicity (below w).asIdeal (Ideal.span {(H.g 1 : OF H.E)}) +
        emultiplicity (below w).asIdeal (Ideal.span {(H.pde : OF H.E)}) +
        emultiplicity (below w).asIdeal (Ideal.span {(H.pde' : OF H.E)})) +
      emultiplicity (below w).asIdeal (below w0).asIdeal :=
    emult_cond (below w) (below w0) (H.g 0) (H.g 1) H.pde H.pde'
  have qw : below w = below w0 → (q0 : 𝓞 H.E) ∈ w.asIdeal := fun heq =>
    (mem_below w q0).mp (heq ▸ (mem_below w0 q0).mpr hq0)
  have toExp : ∀ n : ℕ, emultiplicity (below w).asIdeal (cond0 H w0) = n → expIn (cond0 H w0) (below w) = n :=
    fun n h => multiplicity_eq_of_emultiplicity_eq_some h
  have m0 : (H.g 0 : 𝓞 H.E) ∈ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.g 0 : OF H.E)}) = 1 :=
    emult_one w (pr _ (by simp)) (dc _ (by simp))
  have m1 : (H.g 1 : 𝓞 H.E) ∈ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.g 1 : OF H.E)}) = 1 :=
    emult_one w (pr _ (by simp)) (dc _ (by simp))
  have m2 : (H.pde : 𝓞 H.E) ∈ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.pde : OF H.E)}) = 1 :=
    emult_one w (pr _ (by simp)) (dc _ (by simp))
  have m3 : (H.pde' : 𝓞 H.E) ∈ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.pde' : OF H.E)}) = 1 :=
    emult_one w (pr _ (by simp)) (dc _ (by simp))
  have n0 : (H.g 0 : 𝓞 H.E) ∉ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.g 0 : OF H.E)}) = 0 :=
    emult_zero w
  have n1 : (H.g 1 : 𝓞 H.E) ∉ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.g 1 : OF H.E)}) = 0 :=
    emult_zero w
  have n2 : (H.pde : 𝓞 H.E) ∉ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.pde : OF H.E)}) = 0 :=
    emult_zero w
  have n3 : (H.pde' : 𝓞 H.E) ∉ w.asIdeal → emultiplicity (below w).asIdeal (Ideal.span {(H.pde' : OF H.E)}) = 0 :=
    emult_zero w
  have u := fun x (hx : x ∈ [H.g 0, H.g 1, H.pde, H.pde', q0]) y (hy : y ∈ [H.g 0, H.g 1, H.pde, H.pde', q0])
    (hne : x ≠ y) (mx : (x : 𝓞 H.E) ∈ w.asIdeal) (my : (y : 𝓞 H.E) ∈ w.asIdeal) => hne (uniq x hx y hy mx my)
  refine ⟨fun hO => ?_, fun heq => ?_, fun hO hne => ?_⟩
  · have hne : below w ≠ below w0 := by
      intro heq
      have hq := qw heq
      rcases hO with ⟨k, hk⟩ | hk | hk
      · fin_cases k
        · have hk : (H.g 0 : 𝓞 H.E) ∈ w.asIdeal := hk
          exact u _ (by simp) _ (by simp) (by omega) hk hq
        · have hk : (H.g 1 : 𝓞 H.E) ∈ w.asIdeal := hk
          exact u _ (by simp) _ (by simp) (by omega) hk hq
      · exact u _ (by simp) _ (by simp) (by omega) hk hq
      · exact u _ (by simp) _ (by simp) (by omega) hk hq
    apply toExp
    rw [key, emult_ne hne]
    rcases hO with ⟨k, hk⟩ | hk | hk
    · fin_cases k
      · have hk : (H.g 0 : 𝓞 H.E) ∈ w.asIdeal := hk
        rw [m0 hk, n1 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
          n2 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
          n3 (fun h => u _ (by simp) _ (by simp) (by omega) hk h)]
        norm_num
      · have hk : (H.g 1 : 𝓞 H.E) ∈ w.asIdeal := hk
        rw [m1 hk, n0 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
          n2 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
          n3 (fun h => u _ (by simp) _ (by simp) (by omega) hk h)]
        norm_num
    · have hk : (H.pde : 𝓞 H.E) ∈ w.asIdeal := hk
      rw [m2 hk, n0 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
        n1 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
        n3 (fun h => u _ (by simp) _ (by simp) (by omega) hk h)]
      norm_num
    · have hk : (H.pde' : 𝓞 H.E) ∈ w.asIdeal := hk
      rw [m3 hk, n0 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
        n1 (fun h => u _ (by simp) _ (by simp) (by omega) hk h),
        n2 (fun h => u _ (by simp) _ (by simp) (by omega) hk h)]
      norm_num
  · have hq := qw heq
    have a0 : (H.g 0 : 𝓞 H.E) ∉ w.asIdeal := fun h => u _ (by simp) _ (by simp) (by omega) hq h
    have a1 : (H.g 1 : 𝓞 H.E) ∉ w.asIdeal := fun h => u _ (by simp) _ (by simp) (by omega) hq h
    have a2 : (H.pde : 𝓞 H.E) ∉ w.asIdeal := fun h => u _ (by simp) _ (by simp) (by omega) hq h
    have a3 : (H.pde' : 𝓞 H.E) ∉ w.asIdeal := fun h => u _ (by simp) _ (by simp) (by omega) hq h
    refine ⟨?_, ?_⟩
    · rintro (⟨k, hk⟩ | hk | hk)
      · fin_cases k
        · exact a0 hk
        · exact a1 hk
      · exact a2 hk
      · exact a3 hk
    · apply toExp
      rw [key, n0 a0, n1 a1, n2 a2, n3 a3, heq, emult_self]
      norm_num
  · have a0 : (H.g 0 : 𝓞 H.E) ∉ w.asIdeal := fun h => hO (Or.inl ⟨0, h⟩)
    have a1 : (H.g 1 : 𝓞 H.E) ∉ w.asIdeal := fun h => hO (Or.inl ⟨1, h⟩)
    have a2 : (H.pde : 𝓞 H.E) ∉ w.asIdeal := fun h => hO (Or.inr (Or.inl h))
    have a3 : (H.pde' : 𝓞 H.E) ∉ w.asIdeal := fun h => hO (Or.inr (Or.inr h))
    apply toExp
    rw [key, n0 a0, n1 a1, n2 a2, n3 a3, emult_ne hne]
    norm_num

end GlobalTheory.LamTie
end

section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

theorem _root_.GlobalTheory.T.exists_fontaineTheta_frobeniusInverse_shift : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (n : ℕ), ∃ θ : Ainf l →ₐ[ℤ_[l]] OC l, IsThetaShift AI n θ := by
  first | exact @GlobalTheory.Cyc.Decomp.exists_isThetaShift | exact GlobalTheory.Cyc.Decomp.exists_isThetaShift | (intros; apply GlobalTheory.Cyc.Decomp.exists_isThetaShift <;> assumption)
end
