module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1374
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle272
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle082
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle090
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle078
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1152
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1512
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1636
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1633
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
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
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

set_option autoImplicit false

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelUnique

theorem mem_map_prod {O S : Type} [CommRing O] [IsDedekindDomain O] [CommRing S] (f : O →+* S)
    (T : Finset (HeightOneSpectrum O)) {s : S} (h : ∀ P ∈ T, s ∈ P.asIdeal.map f) :
    s ∈ (∏ P ∈ T, P.asIdeal).map f := by
  have e : (∏ P ∈ T, P.asIdeal).map f = ∏ P ∈ T, P.asIdeal.map f := map_prod (Ideal.mapHom f) _ _
  rw [e, Ideal.prod_eq_iInf_of_pairwise_isCoprime (J := fun P : HeightOneSpectrum O => P.asIdeal.map f) fun P _ Q _ hne =>
    (HeightOneSpectrum.isCoprime_of_ne P Q hne).map (Ideal.mapHom f)]
  exact Ideal.mem_iInf.2 fun P => Ideal.mem_iInf.2 fun hP => h P hP

section Res

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem sub_mem_idS {P : Pl E} {s t : Formalism.L2.Herm.intAf F E} (h : resS F P s = resS F P t) : s - t ∈ idS F P.asIdeal :=
  Ideal.Quotient.eq.1 ((RingEquiv.ofBijective (cmpS F P.asIdeal) (cmpS_bij (F := F) P.asIdeal P.ne_bot)).symm.injective h)

theorem exists_matrix (T : Finset (Pl E)) {J : Ideal (𝓞 E)} {M : ℕ}
    (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 E)}) {y y' : GL (Fin n) (Formalism.L2.Herm.intAf F E)}
    (h : ∀ P ∈ T, Formalism.UG.bc (resS F P) y = Formalism.UG.bc (resS F P) y') {b : 𝓞 E} (hb : b ∈ J) :
    ∃ s : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E), oToS F E b • (y.1 - y'.1) = M • s := by
  have key : ∀ i j, ∃ c, oToS F E b * (y.1 i j - y'.1 i j) = M • c := by
    intro i j
    have h1 : y.1 i j - y'.1 i j ∈ (∏ P ∈ T, P.asIdeal).map (oToS F E) :=
      mem_map_prod _ T fun P hP => sub_mem_idS (congrArg (fun g : GL (Fin n) (kP P) => g.1 i j) (h P hP))
    have h2 := Ideal.mul_mem_mul h1 (Ideal.mem_map_of_mem (oToS F E) hb)
    rw [← Ideal.map_mul, hJ, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.mem_span_singleton'] at h2
    obtain ⟨c, hc⟩ := h2
    exact ⟨c, by rw [mul_comm, ← hc, nsmul_eq_mul, mul_comm]⟩
  choose c hc using key
  exact ⟨Matrix.of c, Matrix.ext fun i j => hc i j⟩

end Res

theorem conj_mulVec_mem {R : Type} [CommRing R] {n : ℕ} (S : Subring R) (β : GL (Fin n) R) (s : Matrix (Fin n) (Fin n) S)
    (z : Fin n → R) (hz : ∀ j, ((β⁻¹).1 *ᵥ z) j ∈ S) (i : Fin n) :
    ((β⁻¹).1 *ᵥ ((β.1 * s.map S.subtype * (β⁻¹).1) *ᵥ z)) i ∈ S := by
  rw [Matrix.mulVec_mulVec, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, ← Matrix.mulVec_mulVec]
  generalize (β⁻¹).1 *ᵥ z = w at hz
  exact Subring.sum_mem S (t := Finset.univ) (f := fun j => (s i j : R) * w j) fun j _ => mul_mem (s i j).2 (hz j)

theorem conj_smul_sub {R : Type} [CommRing R] {n : ℕ} (S : Subring R) (β : GL (Fin n) R) {y y' : GL (Fin n) S}
    {s : Matrix (Fin n) (Fin n) S} {b : S} {M : ℕ} (h : b • (y.1 - y'.1) = M • s) :
    (b : R) • ((β * Formalism.UG.bc S.subtype y * β⁻¹).1 - (β * Formalism.UG.bc S.subtype y' * β⁻¹).1) =
      M • (β.1 * s.map S.subtype * (β⁻¹).1) := by
  have e : (b : R) • ((Formalism.UG.bc S.subtype y).1 - (Formalism.UG.bc S.subtype y').1) = M • s.map S.subtype := by
    ext i j
    have := congrArg (fun m : Matrix (Fin n) (Fin n) S => S.subtype (m i j)) h
    simp only [Matrix.smul_apply, map_nsmul, smul_eq_mul, map_mul, Matrix.sub_apply, map_sub] at this
    exact this
  rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, ← sub_mul, ← mul_sub, ← smul_mul_assoc, ← mul_smul_comm, e,
    mul_smul_comm, smul_mul_assoc]

theorem exists_matrix_hat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} {Λ : Submodule (𝓞 E) (Fin n → E)} (hfr : IsFrame β Λ)
    (T : Finset (Pl E)) {J : Ideal (𝓞 E)} {M : ℕ} (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 E)})
    {x x' : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hx : x ∈ St β) (hx' : x' ∈ St β)
    (h : ∀ P ∈ T, redFn β P x = redFn β P x') {b : 𝓞 E} (hb : b ∈ J)
    {K K' : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)}
    (hK : ∀ i j, x.1 i j = Algebra.TensorProduct.comm F _ E (K i j))
    (hK' : ∀ i j, x'.1 i j = Algebra.TensorProduct.comm F _ E (K' i j)) :
    ∃ N : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E),
      (∀ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)), N *ᵥ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E))) ∧
        ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E)) • (K - K') = M • N := by
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨y', rfl⟩ := hx'
  simp only [redFn_frGL] at h
  obtain ⟨s, hs⟩ := exists_matrix T hJ h hb
  have e := conj_smul_sub _ β hs
  have hN := fun z hz => (hfr _).2 (conj_mulVec_mem _ β s z ((hfr z).1 hz))
  generalize β.1 * s.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1 = N at e hN
  refine ⟨N.map (Algebra.TensorProduct.comm F _ E).symm, fun z hz => ?_, Matrix.ext fun i j => ?_⟩
  · have h4 := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ (hN _ (GlobalTheory.PrincInLevel.swap_mem_hatL Λ z hz))
    convert h4 using 1
    ext i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  · apply (Algebra.TensorProduct.comm F _ E).injective
    rw [Matrix.smul_apply, Matrix.smul_apply, map_nsmul, Matrix.map_apply, AlgEquiv.apply_symm_apply, smul_eq_mul, map_mul,
      Matrix.sub_apply, map_sub, ← hK, ← hK']
    exact congrFun (congrFun e i) j

variable {D : D7}

theorem mulVec_mem_latGHat {V : HSp D} (N : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))
    (h : ∀ z ∈ latHat V, N *ᵥ z ∈ latHat V) : ∀ z ∈ latGHat V 1, N *ᵥ z ∈ latGHat V 1 := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, _, ⟨z, hz, rfl⟩, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨a, ha, _, ⟨_, h z hz, rfl⟩, ?_⟩
    rw [GlobalTheory.Member.LatMove.fin_one, GlobalTheory.Member.LatMove.fin_one]
    exact Matrix.mulVec_smul N ((1 : Af D.host.F) ⊗ₜ[D.host.F] a) z
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mulVec_neg]; exact neg_mem hx

theorem exists_cong {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) (T : Finset (Pl D.host.E)) {J : Ideal (𝓞 D.host.E)} {M : ℕ}
    (hJ : (∏ P ∈ T, P.asIdeal) * J = Ideal.span {(M : 𝓞 D.host.E)}) {k k' : GA D V}
    (hk : Lev.finE V k ∈ St β) (hk' : Lev.finE V k' ∈ St β)
    (h : ∀ P ∈ T, redFn β P (Lev.finE V k) = redFn β P (Lev.finE V k')) {b : 𝓞 D.host.E} (hb : b ∈ J) :
    ∀ z ∈ latGHat V 1, ∃ w ∈ latGHat V 1,
      ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • ((finHom V k).1 *ᵥ z - (finHom V k').1 *ᵥ z) = M • w := by
  have hl : latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβ]; exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  obtain ⟨c, hfr, -⟩ := hβ
  obtain ⟨N, hN, e⟩ := exists_matrix_hat hfr T hJ hk hk' h hb (K := (finHom V k).1) (K' := (finHom V k').1)
    (fun _ _ => rfl) (fun _ _ => rfl)
  rw [← hl] at hN
  intro z hz
  refine ⟨_, mulVec_mem_latGHat _ hN z hz, ?_⟩
  rw [← Matrix.sub_mulVec, ← Matrix.smul_mulVec, e, Matrix.smul_mulVec]

theorem redFn_eq_of_lift {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} (hr : V.rank = L.r)
    {g : G0 L.Pg L.r} {k k' : GA D V} (hk : Lev.IsLevelLift V β L g k) (hk' : Lev.IsLevelLift V β L g k') :
    ∀ P ∈ L.Pg, redFn β P (Lev.finE V k) = redFn β P (Lev.finE V k') := by
  intro P hP
  have e : upperLeftBlock L.hr (redFn β P (Lev.finE V k)) = upperLeftBlock L.hr (redFn β P (Lev.finE V k')) :=
    congrFun (hk.2.2.trans hk'.2.2.symm) ⟨P, hP⟩
  have e' := congrArg Units.val e
  rw [upper_block_val_submatrix _ (blockTri_blkOf_le _ _ (parLev_g hk.2.1 hP)),
    upper_block_val_submatrix _ (blockTri_blkOf_le _ _ (parLev_g hk'.2.1 hP))] at e'
  exact Units.ext (Matrix.ext fun i j => congrFun (congrFun e' (Fin.cast hr i)) (Fin.cast hr j))

theorem sub_eq_nsmul {R : Type} [CommRing R] {n : ℕ} {K K' : Matrix (Fin n) (Fin n) R} {t : R} {x x' z w₁ w₂ w₃ : Fin n → R}
    {M : ℕ} (e₁ : x - K *ᵥ (t • z) = M • w₁) (e₂ : x' - K' *ᵥ (t • z) = M • w₂) (e₃ : t • (K *ᵥ z - K' *ᵥ z) = M • w₃) :
    x - x' = M • (w₁ - w₂ + w₃) := by
  rw [smul_add, smul_sub M, ← e₁, ← e₂, ← e₃, Matrix.mulVec_smul, Matrix.mulVec_smul, smul_sub]
  abel

theorem sub_mem_of_approx {V : HSp D} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {I J : Ideal (𝓞 D.host.E)} {M : ℕ} (hM : 0 < M)
    (hI : (M : 𝓞 D.host.E) ∈ I) (hIJ : I ⊔ J = ⊤)
    {K K' : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)}
    (h : ∀ b ∈ J, ∀ z ∈ latGHat V 1, ∃ w ∈ latGHat V 1,
      ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((b : 𝓞 D.host.E) : D.host.E)) • (K *ᵥ z - K' *ᵥ z) = M • w)
    {f f' : La →ₗ[𝓞 D.host.E] La}
    (hf : ∀ a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
      finVec V (ι (f a)) - K *ᵥ finVec V (ι a) = M • w)
    (hf' : ∀ a ∈ J • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
      finVec V (ι (f' a)) - K' *ᵥ finVec V (ι a) = M • w) (a : La) :
    f a - f' a ∈ I • (⊤ : Submodule (𝓞 D.host.E) La) := by
  have hm : ∀ a, ι a ∈ latG V 1 := fun a => hι.2 ▸ LinearMap.mem_range_self ι a
  have h5 := (GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.1
  obtain ⟨u, hu, b, hb, hub⟩ := Submodule.mem_sup.1 (hIJ ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ I ⊔ J)
  rw [← one_smul (𝓞 D.host.E) (f a - f' a), ← hub, add_smul]
  refine add_mem (Submodule.smul_mem_smul hu Submodule.mem_top) ?_
  obtain ⟨w₁, hw₁, e₁⟩ := hf (b • a) (Submodule.smul_mem_smul hb Submodule.mem_top)
  obtain ⟨w₂, hw₂, e₂⟩ := hf' (b • a) (Submodule.smul_mem_smul hb Submodule.mem_top)
  obtain ⟨w₃, hw₃, e₃⟩ := h b hb _ ((GlobalTheory.Member.LatMove.mem_lat_iff V 1 _).1 (hm a))
  have e₀ : finVec V (ι (b • a)) = ((1 : Af D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • finVec V (ι a) := by
    rw [map_smul]; exact GlobalTheory.AdLat.Tower.fv_smul b (ι a)
  have e₄ : finVec V (ι (b • (f a - f' a))) = finVec V (ι (f (b • a))) - finVec V (ι (f' (b • a))) := by
    rw [smul_sub, ← map_smul f, ← map_smul f', map_sub]; exact GlobalTheory.AdLat.Tower.fv_sub _ _
  have e₅ : finVec V (ι (b • (f a - f' a))) = M • (w₁ - w₂ + w₃) := by
    rw [e₀] at e₁ e₂
    exact e₄.trans (sub_eq_nsmul e₁ e₂ e₃)
  obtain ⟨⟨v, hv⟩, ev⟩ := GlobalTheory.AdLat.Tower.exists_div (F := D.host.F) (M := latG V 1)
    (fun v => h5 ▸ (GlobalTheory.Member.LatMove.mem_lat_iff V 1 v).symm) hM ⟨_, hm (b • (f a - f' a))⟩
    (h5 ▸ add_mem (sub_mem hw₁ hw₂) hw₃) e₅
  obtain ⟨c, rfl⟩ : v ∈ LinearMap.range ι := hι.2 ▸ hv
  have e₆ : b • (f a - f' a) = (M : 𝓞 D.host.E) • c := by
    apply hι.1
    rw [Nat.cast_smul_eq_nsmul, map_nsmul]
    exact congrArg Subtype.val ev
  rw [e₆]
  exact Submodule.smul_mem_smul hI Submodule.mem_top

theorem levUnique (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (hL : R.toLevCh.Is A.μ0) (hT : LawsJ T)
    (hM : T.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal) (i : Fin D.R.m) : GlobalTheory.OneMapAllCompare.LevUnique T R i := by
  intro lev lev' h h' g a
  obtain ⟨k, hk, hf⟩ := h g
  obtain ⟨k', hk', hf'⟩ := h' g
  have hp : T.Q.l.Mb * Mfr T.Q.l = Ideal.span {((T.Q.l.M : ℕ) : 𝓞 D.host.E)} := T.Q.l.prod
  have hp' : (∏ PP ∈ R.Pg, PP.asIdeal) * Mfr T.Q.l = Ideal.span {((T.Q.l.M : ℕ) : 𝓞 D.host.E)} := by rw [← hM]; exact hp
  have hI : ((T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ T.Q.l.Mb :=
    (hp.ge.trans (Ideal.mul_le_inf.trans inf_le_left)) (Ideal.mem_span_singleton_self _)
  have hc : T.Q.l.Mb ⊔ Mfr T.Q.l = ⊤ := T.Q.l.coprime
  have hr := redFn_eq_of_lift (L := R.datWp i R.triv) (rank_Wc i) hk hk'
  have hcong := fun b hb => exists_cong (b := b) (hL.βW i) R.Pg hp' (parLev_St hk.2.1) (parLev_St hk'.2.1) hr hb
  exact sub_mem_of_approx (GlobalTheory.LevelAction.latEmb_iotaW T hT i) (lt_of_lt_of_le (by norm_num) T.Q.l.three_le) hI hc hcong hf hf' a

end GlobalTheory.LevelUnique
end

section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift.Transl

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

theorem lifts (hL : R.toLevCh.Is A.μ0) : Lev.LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv) := by
  have h := hL.βW i
  obtain ⟨c, hc⟩ := h
  exact GlobalTheory.FiniteGroupLifts.liftsExist_of_twist_empty _ _ _ _ _ hc rfl
    (GlobalTheory.TypePlaces.not_isConjPl R.C.P R.Pg hL.Pg)

theorem levChi_flag (k : GA D (Wc D i)) : Lev.levChi (Wc D i) (R.βW i) (Lev.flagL (R.datWp i R.triv)) k = 1 := by
  have h2 : ext1 (Lev.flagL (R.datWp i R.triv)).P.H (Lev.flagL (R.datWp i R.triv)).P.chi
      (rTup (R.βW i) (Lev.flagL (R.datWp i R.triv)) (Lev.finE (Wc D i) k)) = 1 := Lev.subgroupCharExtension_one_apply _ _
  unfold Lev.levChi levFn
  rw [h2, show (Lev.flagL (R.datWp i R.triv)).s = 0 from rfl, Finset.range_zero,
    show (Lev.flagL (R.datWp i R.triv)).Q = ∅ from rfl, Finset.prod_empty]
  simp only [Finset.prod_empty, Finset.prod_const_one, mul_one, Units.val_one]

theorem hasType (hW : R.models_HW) (σ : D.what₂.LL →+* ℂ) (y : (R.HW i σ).H) (v : (R.MW i σ).Vec) :
    Lev.HasType (Wc D i) (R.βW i) (Lev.flag1L (R.datWp i R.triv)) ((R.HW i σ).e y v) := by
  have hm : (R.HW i σ).e y ∈ R.Wall i σ := (hW i σ).2.1.le (LinearMap.mem_range_self _ y)
  exact fun κ hκ h => ((GlobalTheory.MultMem.mem_mult_iff ..).1 hm).lev v κ hκ h

theorem transl (hW : R.models_HW) (hg : R.models_gW) (σ : D.what₂.LL →+* ℂ) (g : G) (k : GA D (Wc D i))
    (hk : IsLiftW R i g k) (y : (R.HW i σ).H) (v : (R.MW i σ).Vec) (h : GA D (Wc D i)) :
    (R.HW i σ).e (R.gW i σ g y) v h = (R.HW i σ).e y v (h * k) := by
  have h1 := Lev.level_action_spec (hasType R i hW σ y v) ⟨k, hk⟩ k hk h
  have h2 : (R.HW i σ).e (R.gW i σ g y) v h =
      Lev.actG0 (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) ((R.HW i σ).e y v) h :=
    congrArg (fun U : MMap (R.MW i σ) => U v h) (hg i σ g y)
  refine h2.trans (h1.trans ?_)
  rw [levChi_flag, inv_one, one_mul]

theorem sum_apply_eq {G X Y : Type} [Fintype G] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ev : X →ₗ[ℂ] Y) (c : G → ℂ) (a : G → Y →ₗ[ℂ] Y) (b : G → X) (y : Y) (h : ∀ g, ev (b g) = a g y) :
    (∑ g, c g • a g) y = ev (∑ g, c g • b g) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, h]

theorem proj (hg : R.models_gW) (σ : D.what₂.LL →+* ℂ) (y : (R.HW i σ).H) (v : (R.MW i σ).Vec) :
    R.eWf i σ ((R.HW i σ).e y v) = (R.HW i σ).e (∑ g, RealDat.eC (A := A) σ g • R.gW i σ g y) v :=
  sum_apply_eq
    (({ toFun := fun U => U v, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } :
      MMap (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ)) ∘ₗ (R.HW i σ).e)
    (RealDat.eC (A := A) σ) (fun g => actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) (fun g => R.gW i σ g y)
    ((R.HW i σ).e y v) fun g => congrArg (fun U : MMap (R.MW i σ) => U v) (hg i σ g y)

end GlobalTheory.GalLift.Transl

namespace GlobalTheory.GalLift

end GlobalTheory.GalLift

end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.StabFin

theorem norm_le_one_at_u : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (r : ℕ) (z : Gr G r) (K : Subgroup (Gr G r)) (g : Gr G r), 0 < r → Subgroup.Commensurable K (KHT p G.m G.n r G.Fw) → ∀ w : P.cent, P.toQr r z w ∈ K.map (MulAut.conj g).toMonoidHom → ∀ (a : FM P), jM P a = ((w : G.Cˣ × ℚˣ).1 : G.C) → ∀ τ : FM P →+* PadicAlgCl p, LiesOver G.Kq G.u (τ.comp (algebraMap G.F (FM P))) → ‖τ a‖ ≤ 1 := by
  intro p _ G P r z K g _ hK w hw a ha τ hτ
  obtain ⟨i, σ, hσ⟩ := G.emb_all _ hτ
  set τ' : FM P →+* PadicAlgCl p := ((σ.symm : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p).comp τ with hτ'
  have hτ'F : τ'.comp (algebraMap G.F (FM P)) = G.emb i := by
    rw [hτ', RingHom.comp_assoc, hσ]
    ext x; simp
  have hnorm : ‖τ a‖ = ‖τ' a‖ := by
    have : τ a = σ (τ' a) := by simp [hτ']
    rw [this]; exact (spectralNorm_eq_of_equiv σ _).symm
  rw [hnorm]
  obtain ⟨m, hm0, hm⟩ := exists_pow_mem_conj K (KHT p G.m G.n r G.Fw) g _ hK hw
  obtain ⟨k, hk, hkeq⟩ := hm
  obtain ⟨v, hv0, hv⟩ := GlobalTheory.T.exists_common_eigenvector_rho_adjoinRoot_embedding p G P i τ' hτ'F
  have hjm : jM P (a ^ m) = (((w ^ m : P.cent) : G.Cˣ × ℚˣ).1 : G.C) := by
    rw [map_pow, ha]; rfl
  have key : (z * g) * k * (z * g)⁻¹ = inclG G r (locC G ((w ^ m : P.cent) : G.Cˣ × ℚˣ)) := by
    have e : P.toQr r z (w ^ m) = z⁻¹ * inclG G r (locC G ((w ^ m : P.cent) : G.Cˣ × ℚˣ)) * z := rfl
    rw [map_pow] at e
    rw [← hkeq] at e
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e
    have e2 : inclG G r (locC G ((w ^ m : P.cent) : G.Cˣ × ℚˣ)) =
        z * (z⁻¹ * inclG G r (locC G ((w ^ m : P.cent) : G.Cˣ × ℚˣ)) * z) * z⁻¹ := by group
    rw [e2, ← e]
    group
  have hcomp := congrArg (fun x : Gr G r => ((x.2 i : GL (Fin G.n) (KQ p (G.Fw i) r)) : Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw i) r))) key
  have hk' : k.2 i ∈ Kres p (G.Fw i) G.n r := hk.2 i (Set.mem_univ _)
  have hb := GlobalTheory.T.eigenvalue_integral_norm_bound p (G.Fw i) G.n r (G.rho i (jM P (a ^ m))) ((z * g).2 i) (k.2 i) hk'
    (by rw [hjm]; exact hcomp.symm) v (τ' (a ^ m)) hv0 (hv _)
  rw [map_pow, norm_pow] at hb
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hm0.ne').1 hb

end GlobalTheory.StabFin
end
end

section

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

namespace GlobalTheory.AutGrowth.KilledFin

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem cap_commute_Zalg (τ : E →+* ℂ) (u : ℂ) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    Commute (cap τ u) z :=
  commute_Zalg (fun X => GlobalTheory.SpehInfChar.cap_commute_act τ u (.lie X)) hz

theorem Zalg_commute {z z' : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) (hz' : z' ∈ Zalg E a) :
    Commute z z' := by
  have hle : Zalg E a ≤ Subalgebra.centralizer ℂ {z'} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨τ, u, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact (cap_commute_Zalg τ u hz').eq.symm
  have h := hle hz
  rw [Subalgebra.mem_centralizer_iff] at h
  exact (h z' rfl).symm

variable (φ : Sm E a) (L : Subgroup (GL (Fin a) (Af E)))

def postZ (z : Module.End ℂ (Sm E a)) (hz : z ∈ Zalg E a) : Module.End ℂ (mapsJ φ L) where
  toFun T := ⟨z ∘ₗ T.1, by
    have hT : T.1 ∈ maps L (spanK E a φ) (spanK_stable φ) ∧
        ∀ z ∈ Zalg E a, z φ = 0 → ∀ w, z (T.1 w) = 0 := T.2
    show _ ∧ _
    refine ⟨GlobalTheory.T.centre_comp_mem_kinfEquivariantAutomorphicMaps E a L (spanK E a φ) (spanK_stable φ) T.1 hT.1 z hz, fun z' hz' h0 w => ?_⟩
    show z' (z (T.1 w)) = 0
    rw [← Module.End.mul_apply, ← (Zalg_commute hz hz').eq, Module.End.mul_apply, hT.2 z' hz' h0 w, map_zero]⟩
  map_add' T T' := by ext; simp
  map_smul' c T := by ext; simp

def postZAlg : Zalg E a →ₐ[ℂ] Module.End ℂ (mapsJ φ L) where
  toFun z := postZ φ L z.1 z.2
  map_one' := LinearMap.ext fun _ => Subtype.ext (LinearMap.ext fun _ => rfl)
  map_mul' _ _ := LinearMap.ext fun _ => Subtype.ext (LinearMap.ext fun _ => rfl)
  map_zero' := LinearMap.ext fun _ => Subtype.ext (LinearMap.ext fun _ => rfl)
  map_add' _ _ := LinearMap.ext fun _ => Subtype.ext (LinearMap.ext fun _ => rfl)
  commutes' _ := LinearMap.ext fun _ => Subtype.ext (LinearMap.ext fun _ => rfl)

end GlobalTheory.AutGrowth.KilledFin

namespace GlobalTheory.AutGrowth.KilledFin

theorem fd_adjoin_of_ker_le (M : Type) [AddCommGroup M] [Module ℂ M] (A : Type) [Ring A] [Algebra ℂ A]
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : A →ₐ[ℂ] Module.End ℂ M) (ev : A →ₗ[ℂ] V)
    (hev : FiniteDimensional ℂ (LinearMap.range ev)) (hker : LinearMap.ker ev ≤ LinearMap.ker ρ.toLinearMap)
    (S : Set (Module.End ℂ M)) (hS : S ⊆ ρ.range) : FiniteDimensional ℂ (Algebra.adjoin ℂ S) := by
  haveI : FiniteDimensional ℂ (A ⧸ LinearMap.ker ev) :=
    LinearEquiv.finiteDimensional (ev.quotKerEquivRange).symm
  have hR : FiniteDimensional ℂ (LinearMap.range ρ.toLinearMap) := by
    rw [← Submodule.range_liftQ (LinearMap.ker ev) ρ.toLinearMap hker]
    infer_instance
  have hle : Subalgebra.toSubmodule (Algebra.adjoin ℂ S) ≤ LinearMap.range ρ.toLinearMap := by
    intro x hx
    obtain ⟨y, rfl⟩ := Algebra.adjoin_le hS hx
    exact ⟨y, rfl⟩
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.AutGrowth.KilledFin

namespace GlobalTheory.AutGrowth.KilledFin

theorem finiteDimensional_mapsJ : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → ∀ L : Subgroup (GL (Fin a) (Af E)),
    IsOpen (L : Set (GL (Fin a) (Af E))) → FiniteDimensional ℂ (mapsJ φ L) := by
  intro hP E _ _ _ a φ hφ L hL
  have hcap : ∀ (τ : E →+* ℂ) (u : ℂ), cap (a := a) τ u ∈ Zalg E a := fun τ u =>
    Algebra.subset_adjoin ⟨τ, u, rfl⟩
  let S : Set (Module.End ℂ (mapsJ φ L)) := {s | ∃ τ u, s = postZ φ L (cap τ u) (hcap τ u)}
  refine GlobalTheory.T.finiteDimensional_of_commuting_finiteAlgebra_jointEigen (mapsJ φ L) S ?_ ?_ ?_
  · rintro _ ⟨τ, u, rfl⟩ _ ⟨τ', u', rfl⟩
    refine LinearMap.ext fun T => Subtype.ext (LinearMap.ext fun w => ?_)
    show cap τ u (cap τ' u' (T.1 w)) = cap τ' u' (cap τ u (T.1 w))
    rw [← Module.End.mul_apply, (Zalg_commute (hcap τ u) (hcap τ' u')).eq, Module.End.mul_apply]
  · let ev : Zalg E a →ₗ[ℂ] Sm E a := (LinearMap.applyₗ φ).comp (Zalg E a).val.toLinearMap
    have hker : LinearMap.ker ev ≤ LinearMap.ker (postZAlg φ L).toLinearMap := by
      intro z hz
      rw [LinearMap.mem_ker] at hz ⊢
      refine LinearMap.ext fun T => Subtype.ext (LinearMap.ext fun w => ?_)
      have hT : T.1 ∈ maps L (spanK E a φ) (spanK_stable φ) ∧
          ∀ z ∈ Zalg E a, z φ = 0 → ∀ w, z (T.1 w) = 0 := T.2
      exact hT.2 z.1 z.2 hz w
    have hev : FiniteDimensional ℂ (LinearMap.range ev) := by
      have h1 : LinearMap.range ev ≤
          Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) := by
        rintro _ ⟨z, rfl⟩
        exact Submodule.subset_span ⟨z.1, z.2, rfl⟩
      haveI := hφ.zfin
      exact Submodule.finiteDimensional_of_le h1
    refine fd_adjoin_of_ker_le (mapsJ φ L) (Zalg E a) (Sm E a) (postZAlg φ L) ev hev hker S ?_
    rintro _ ⟨τ, u, rfl⟩
    exact ⟨⟨cap τ u, hcap τ u⟩, rfl⟩
  · intro c
    let J := ⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ (mapsJ φ L)) (c s))
    let N : Submodule ℂ (spanK E a φ →ₗ[ℂ] Sm E a) := J.map (mapsJ φ L).subtype
    have hNle : N ≤ maps L (spanK E a φ) (spanK_stable φ) := by
      rintro _ ⟨T, _, rfl⟩
      have hT : T.1 ∈ maps L (spanK E a φ) (spanK_stable φ) ∧
          ∀ z ∈ Zalg E a, z φ = 0 → ∀ w, z (T.1 w) = 0 := T.2
      exact hT.1
    have hNe : ∀ T ∈ N, ∀ (τ : E →+* ℂ) (u : ℂ),
        cap τ u ∘ₗ T = c (postZ φ L (cap τ u) (hcap τ u)) • T := by
      rintro _ ⟨T, hT, rfl⟩ τ u
      have hT' : T ∈ ⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ (mapsJ φ L)) (c s)) := hT
      have h := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hT' (postZ φ L (cap τ u) (hcap τ u))) ⟨τ, u, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, Module.algebraMap_end_apply] at h
      exact congrArg Subtype.val h
    have hN : FiniteDimensional ℂ N :=
      GlobalTheory.T.finiteDimensional_eigen_intertwiners hP E a L hL (spanK E a φ) (spanK_stable φ) hφ.kfin
        (fun τ u => c (postZ φ L (cap τ u) (hcap τ u))) N hNle hNe
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective (mapsJ φ L).subtype Subtype.val_injective J).symm

end GlobalTheory.AutGrowth.KilledFin
end
end
